import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard012
open N4R2OuterLeftReplay

-- Cycle fingerprint 009a110a36d15859c175a32f321c6da3a1f4e661bdcb15157fcda1c5bc87f9fc.
def localCycle00000 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 4, .distance 1 3, .distance 3 5, .distance 0 3]
    constant := ![0, -1, 0, 0, 1, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 19 1, .triangle 20 0, .triangle 10 0]

-- Cycle fingerprint 025718d17ac27e398d87d21977a3a68497eb339823eb34bd4c2ae408f3c64166.
def localCycle00001 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 026353ddd71152ee152351de28463ce3ce66d6e24dcb5664be94057a8194bb6a.
def localCycle00002 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 1 4, .triangle 20 2, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint 029f9971d30cfd20b26155820562ed5e6084d94cb14916624eac0d0b0e5cd022.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 7 2, .triangle 12 1, .corridorLower 4 5]

-- Cycle fingerprint 02ec389b3c7ba3fcbd5eb0ee5a1fa65ee42da7038b90fdc8467f20c5ff222046.
def localCycle00004 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3]

-- Cycle fingerprint 034013483a5473229f6ae465b161f91840801e95c6020caf5af81a99463f79e7.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 24 1, .triangle 20 1, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 03f7ac870d26a8686894dc38a883ea61fe764b41e7b0afce2acf4d04664ceec6.
def localCycle00006 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5]
    constant := ![-2, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 17 2]

-- Cycle fingerprint 040f8e479b9e3c87f2b7360ccb9d20d945aa00f8e73e36dd944fabd5fd09db53.
def localCycle00007 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 18 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 04833ee3ece3a7d25aaf4ddfc20f7dcb8c63a1e95519ebe494668e604d28a5fb.
def localCycle00008 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, 0, -2, 0, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, true, false, false, true] }
  origin := ![.triangle 16 0, .triangle 18 2, .gapLower 1 3, .triangle 3 2, .triangle 12 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 050bf5d02861d3d79d831c5cbf404474e76ece2c37bde918b89f64e9f7f4b6c9.
def localCycle00009 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 05144428d8d666dab3e22de4af3c91728d46033ecbc47119b3ac4fb7b0313e8b.
def localCycle00010 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 053925899e6587d9b1b7b3e3e9f8f14d0470934bfcca14b691bd297446e09058.
def localCycle00011 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 32 0, .triangle 29 0, .gapLower 2 3, .triangle 26 0, .corridorLower 3 5]

-- Cycle fingerprint 0611b0b6cd563623eb224ec84cbabe8c83591210f5fe1736f1e27681d6d038b0.
def localCycle00012 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 0684fb35e7839acc9e102c2e409ff485dc5410bce57f3043991a75d47c691b42.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 072ea027891b33e3b284698dffcd9a521a378b7f612e90e430f7761f226b0629.
def localCycle00014 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint 07b13ce310877dd96c2ded4ab924d4fcb312c2d368ab33d7eb2110be6d9210ae.
def localCycle00015 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 083d7b2ad3af4decb39f3f98faecf6b11b43d55515e968022811dfb90118e470.
def localCycle00016 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 08a3b234f93a80f8ef778813b4bc88e7623db00b3c43878ef8c494068d8c381c.
def localCycle00017 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 0 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 2, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 2 2, .triangle 13 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 08aa5ff7cb9cbafdcfc8c446e6d4f7721d06293e38300f7de1015bdd5b7de669.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4]
    constant := ![-1, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 19 0, .gapLower 1 4, .triangle 24 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 08e981218163a0e28e04c3ec13d54613b568252b43e7733dafa9df43e4f0744e.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 2, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 0960a777e6a0f8ed64280dc50e8ce9a35186a3997b732c0fb82adab7b1b14aaf.
def localCycle00020 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 3 5, .distance 1 5, .distance 1 3, .distance 1 2]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 5 4, .gapLower 5 3, .gapLower 1 3, .triangle 15 1]

-- Cycle fingerprint 09dfa431ee781f51624bfc8227f5a650a6db90644b248ac862210637f084d462.
def localCycle00021 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 1 2, .distance 2 5, .distance 1 5]
    constant := ![-2, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .gapUpper 2 2, .triangle 17 2]

-- Cycle fingerprint 0ccecf61284b253e811696ffd5d5a9ba593b420a5d9b13a3870f0f5bf7ea584b.
def localCycle00022 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint 0dbd11454a667c5d96c8dca5c1ef1ba4913d168d4500c164e7116ef42f754b87.
def localCycle00023 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 3, .distance 1 6, .theta 1]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 15 2, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint 0e79bee9964cd71629db4a8c583a8d6d00e0ffb6fa79b6606c8c998ade66b169.
def localCycle00024 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.gapLower 1 6, .triangle 16 1, .triangle 18 0, .triangle 30 1, .triangle 26 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 11045ccc97c1645505d5312dd9fecaf5fc14a2ffe474b16bab1616b1ccd43087.
def localCycle00025 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 110a8c2a9d4c6434100aef3317e786b3f9d2d203a7067149d361bdb8c17323e9.
def localCycle00026 : Cycle where
  length := 11
  data := {
    node := ![.distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![-1, -1, 0, -1, 0, 0, 2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 33 0, .triangle 10 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 24 1]

-- Cycle fingerprint 111eb474326b77ac1ccc902678d6abb6afdc2c19fd4f92cad190178aa51584c5.
def localCycle00027 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, 0, -2, 0, -1, 0, -1, 0, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, true, false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 18 1, .triangle 17 0, .triangle 26 1, .triangle 10 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 118a38a46f3532f899870d16ec2889ed20a4dc301926e76e902be5e7a5d02b45.
def localCycle00028 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 20 1, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 122a8b6b0420c5228fdaf2f64fa772ce6c404cbcb9600661b2c6932281a0c202.
def localCycle00029 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![-2, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint 133b7a7f568d2ee78017f739b79fc6433c54be3c0f6399cd5369867b00d7dd91.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .theta 2]
    constant := ![0, 1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .gapLower 0 2, .gapLower 2 0]

-- Cycle fingerprint 142f6625b360c29a6b0a0479afa7ab31d849a38c288722bd63ad847f4e8e8d21.
def localCycle00031 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 15a9cdf8acf1cce04c7f57692ca20b15b00ace94d247a7b6c6271835fbd5eaa5.
def localCycle00032 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, -1, -2, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 3, .triangle 2 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 1633aa6bf3dd3c9a863df7010434f8fa0977883b720c6467d6f3d1ed15dfc455.
def localCycle00033 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 2 6, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -1, 0, 0, 0, 0, -3, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, true] }
  origin := ![.triangle 16 0, .triangle 18 0, .triangle 30 1, .triangle 26 1, .gapLower 2 1, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 174ae4beae2d9e20e73862a9ea70b2cafb792de60539bebc8fbb4ea64e84ab05.
def localCycle00034 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3]
    constant := ![3, -1, 0, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3]

-- Cycle fingerprint 17ceed8de7b44f004975b66118a91f5937a8fa4e701cc0070f9e7b68b9ef6d56.
def localCycle00035 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 1 5]
    constant := ![0, -2, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 22 2]

-- Cycle fingerprint 17dcbc537767b06d060ccd52d464dc63b6c6a6e412753aa358a072d724edc702.
def localCycle00036 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 18825fe1c4e18cfe5a8007cd2253a26b04506ed510f84ec9bbf169ce2e8ba9aa.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint 18f0bb7ff516ab75da9001162499f4ad9e67141f8dcbaa172f6a37b3acf2089c.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 19e6fac60805da6aaa71c3030c92ba56ca116445d023c7e53df26bb8bdaeba69.
def localCycle00039 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 32 0, .triangle 13 0, .triangle 12 2, .triangle 10 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 1a645ce806eca79dd3af306b6190e7774cfc93ead6690c06965367792fe8cf74.
def localCycle00040 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4]
    constant := ![0, 0, -2, 0, -1, -1, 0, 0, -2, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, true, false, false, false, true, false, true, false, false, false] }
  origin := ![.triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 21 1, .triangle 20 0, .triangle 10 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 1a6d98d9d94c2f2163ea11a4d1cf6fcdc3be6b1d2646327f6266eaceeb456c45.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 6, .distance 1 5, .distance 0 5, .distance 0 3, .theta 3]
    constant := ![3, -1, 0, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 21 2, .gapLower 1 4, .triangle 3 2, .triangle 10 1, .gapLower 3 0]

-- Cycle fingerprint 1af6660d60f65af8e5901b0f5488e9922f9134481c6910af75b8eb59c7450c93.
def localCycle00042 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 1 5]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 2 2, .gapLower 6 5, .triangle 24 0]

-- Cycle fingerprint 1b0528a904bd5dccf6260c19ce0afb96090b9c9e659bde9e3cdbde32e27b3e5f.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 1 3, .triangle 3 2, .triangle 12 1, .corridorLower 4 5]

-- Cycle fingerprint 1b0f15d20b6e7b795cdcb2dca30080376be6908d3049fce1ceb6d2473df1e342.
def localCycle00044 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .triangle 24 2, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint 1b4ccc4f201a161fa4b1f3202e780a9cab155c1066086b137eda04b199d31800.
def localCycle00045 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 2 5, .distance 3 5, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![-2, -2, 0, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .triangle 17 1, .triangle 26 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint 1b7c46c5c3b44417b6cbbe4fa628a19eaf9e71b3e1d3d17b512062bff941040f.
def localCycle00046 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 1c1a9212ab5394d3a732106a114733458a0d4324de2a051b40990e7fbff74050.
def localCycle00047 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6]
    constant := ![0, 0, -1, -2, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 23 2]

-- Cycle fingerprint 1dbfe66f9a8a5314850ed079a6948b4d0d3b91d638ef0d6a7bef8a0344304ba0.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 1de8a4ec91b79a881ec817996fe9faadb045b8da6ee5a25270a24585332f906f.
def localCycle00049 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 1e2b8b194bf447d4fb64c69cec2467584381c06ee1a47aea6b6fccbc9ce51db9.
def localCycle00050 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 6]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 21 2]

-- Cycle fingerprint 1ee8088bfb0350d8c2f9e1a3ee1175df3e1c26c7f2a8297fc07ee04db09660a2.
def localCycle00051 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 3 5, .distance 4 5]
    constant := ![-1, 3, 0, 0, -2, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 20 0, .triangle 31 1]

-- Cycle fingerprint 1ef7ec56d46fd0ac53344b7d55e8470adaa931561ac1f38bd2f949e10a799b23.
def localCycle00052 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 209fbf3b5c39dc2c953407f6515ed400a0b6f4fb4114e6b692eb483ed1fd7832.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5]
    constant := ![-1, 3, 0, 0, -2, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 17 0, .triangle 26 1]

-- Cycle fingerprint 212707d1c4897ac7eb4fb713c4a1625a763075dae5002419feb11f9d46539bdb.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 229210a148f78e976ebeb8e84af4505e350ec8c3fbe187c260838e25e7dc9c01.
def localCycle00055 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3]
    constant := ![0, -1, -1, -1, 0, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0]

-- Cycle fingerprint 230f59f59f2bf39032e43048a1ed5937f9a44d58c03d631a64fecb7682292c9d.
def localCycle00056 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .gapLower 1 2]

-- Cycle fingerprint 231aeb1e58ead85d2acc4e35eec9404eb9ccd610cfa8e1f2762c94313d37bca5.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, -1, -2, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 235237ae1fa971193162c7f5ee56d12badb500544ee83a0e241876807c593b38.
def localCycle00058 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 24121437c829f4977ce7efa938098cb91d0a46d77adbacb190ea5f0224437bb2.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 2489359457ccb53dea061f1de7f57660705b25362b4f83a38c98bf89867bdb26.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 24ba3179a9053286c661b3b2af700606300372f9dedd7d8de48e8b70d1ac4eea.
def localCycle00061 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 4, .gapLower 1 3, .triangle 24 1]

-- Cycle fingerprint 26458611282b0488e7a55dfa7e5d5ecd8761c0cdd0c79cc7d8d1903e7d06ad14.
def localCycle00062 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 26b34a922ec12401d6a63535ac65bbb640e2bfa34609ec9e9826c1db74f8efc2.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -1, 0, 3, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true] }
  origin := ![.triangle 28 0, .corridorLower 4 5, .thetaNext 3, .corridorUpper 1 3, .gapLower 1 4, .gapLower 1 3, .triangle 19 1, .triangle 25 2]

-- Cycle fingerprint 273bcf25ec29f5625804bb99b446008373590371664ced522b8f438b70ba9ba2.
def localCycle00064 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .triangle 34 2, .triangle 23 0]

-- Cycle fingerprint 273ce57af3e29b59ebe281d36d0569ec8d9d62aa98e564d4ef88c5b18eb7813f.
def localCycle00065 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2]
    constant := ![-2, -2, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0]

-- Cycle fingerprint 280b6e17c2e7f29d4d6b50d2d5dcf59d12a15a4261e526f30d652ab3906e9fd0.
def localCycle00066 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, false, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 22 2, .gapLower 1 4, .triangle 24 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 28fea3a39d9a11240b7bd8c40ce2d155f891e87e795567db5dafb2fe4c203453.
def localCycle00067 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 30 1, .triangle 17 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 292bf4752e3f9d66c4a4acc7b04e7720108825aca665bd50d1cb58fc7191fe9d.
def localCycle00068 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint 29f523a73dc0dd011697371eb87963440e14706c4b9dbf88272a701b46c17a13.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4]
    constant := ![0, -3, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint 2a59bbc2e15203f856fc8dd7430a23cc890d999084e8e7a5f958513fdf5b5c2a.
def localCycle00070 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, -1, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 21 2, .gapLower 1 4, .triangle 17 1]

-- Cycle fingerprint 2a84e0af2bddc83de40dadfb29288a1c6bf05493b81766d6d51c9756dacad159.
def localCycle00071 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint 2ad3191abd8a2c72e8fa164697e9064c536db403f603f5c4fac6d4b99f4217d5.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 6, .distance 1 5]
    constant := ![-1, -1, 0, 0, 3, -1, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 21 2, .gapLower 1 4]

-- Cycle fingerprint 2af71584599cd2c1e4b83ae593a98fde5023d76521d423b9691ffa541464f7f1.
def localCycle00073 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 2af823b9eee0f9ded70739b2378307df7b29d24739b37e54f6ef2fd42932830b.
def localCycle00074 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 18 2, .gapLower 1 4, .triangle 15 1]

-- Cycle fingerprint 2b1a3202889fb47008b8ff86a7361dc2b3a236ec22f7eb629d8360c201825c56.
def localCycle00075 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 2bce6387ae51baf26d1f4395ceddca69b39c9c3b254dfbcc3855bc4161b2933d.
def localCycle00076 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint 2dc767f5cebd8cca45ea42256b03ba907fb2fda095f32a62952a50ba558d53b3.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 2de7733255fa8413b0509e891f92d89596ee0462b51f923581730bf745517dbb.
def localCycle00078 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 18 0, .triangle 17 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 2e0e8c8d38814d1a0d11fd33863a0b53a9edbc0a76868f3e02fd56fcfb87587a.
def localCycle00079 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 3, .gapLower 1 4, .gapUpper 5 3]

-- Cycle fingerprint 2f55950e43b0fe401e4c284a2c7c35f360362e110364235a21da250ff4121a65.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 0, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 2f6980f55d2377fba60669eaa1324c97feaa27e7f27a1fa855c15fc5d26457e2.
def localCycle00081 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 32 0, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 303f529585f03c81ac187ee4d3034265a3e55c180d364fbfc0a05dac9aa08425.
def localCycle00082 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .triangle 24 1, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 31c2206412be8aafa78cbeead9f69e0a25752ac8f89e8fe08edf9d5aa5eaecd2.
def localCycle00083 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 31e58d2e7987c4d6bc8a2b928af8df5b3773821a2477be107221321ef9592b2a.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 21 2, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint 323ade28f8caf9f55625036b6468a09d417d880a396facf5892ff0741d400341.
def localCycle00085 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 3263f66f60639555d7f7ccbee43f3c822eb57899d7d919c1ace12dfaa927d81d.
def localCycle00086 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 33269564ce4201f717310950b9f0f36726ee96227190ed97c6e10336e9ff4da0.
def localCycle00087 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, 0, 0, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .triangle 18 2, .gapLower 1 3, .triangle 1 0]

-- Cycle fingerprint 3329bc0c72ffd3ce4c1cfa12fef0fc0b53b547427012ef59d83bb2b3c09f6360.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 332cc52b7029845fffd531f30bd5044cef76231465d7003a6fea911e467a4710.
def localCycle00089 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 357eb6b0d6e9cce2cffc9f50600c3aca24692be7f113dea576f88fce9d659a57.
def localCycle00090 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 1 5]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 6 5, .triangle 24 0]

-- Cycle fingerprint 36588321b9c53ef53abaf9caed1921857b2570a0990ab63ce3ba4ccef51cca0f.
def localCycle00091 : Cycle where
  length := 13
  data := {
    node := ![.distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3]
    constant := ![0, 0, -3, 0, 0, 0, 3, 0, 0, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true, true, false, false, false] }
  origin := ![.gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 10 0]

-- Cycle fingerprint 36b3bada88c33f5ba037fc3ebb030d250c383c7b458a5333466f5d38289dcb56.
def localCycle00092 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, 0, 0, -1, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 33 1, .triangle 20 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 370728bd35eda36a700f60eccb5b8c2962c7270749d01a874b139b8ece9fe302.
def localCycle00093 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 3847dfb933083f2c3b3d2408cb2dd03db876371724a4691a1518ff74473e7965.
def localCycle00094 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 3abdbe3bc647762e9d59dd7ccdfc970c6a157b267bb16d64f843a7c84b6aff1a.
def localCycle00095 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 4, .distance 1 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .triangle 23 2, .gapLower 1 4, .triangle 20 0, .triangle 10 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 3cbc9a3929176f34e5df7f77f560ce02c61d838529f936284566ed3f10063471.
def localCycle00096 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -1, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 3cc3cedd136dd1463c3fd62b4835c7716a852e97df6c4c8dad1d0c947fea52e1.
def localCycle00097 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 3cec7ebf7a45414217e093be2806b1b3ebd0f5b0c20ffae5882a87c6eef29f34.
def localCycle00098 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5]
    constant := ![-3, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 17 2]

-- Cycle fingerprint 3dd905fd92e12dc7f0ac5d272e6b3292227cfdd7c7bedfe9dd91b52410b8227d.
def localCycle00099 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 2 5, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 7 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 3e8b37d242c1553a9abb326db5823a6848ec8c0530b9b80506a83c0588417b40.
def localCycle00100 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 24 0, .triangle 33 0, .triangle 10 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 3eb2fab31d88b18ef7c5ad75aaa11e7c1ac147236603bf5834fabba9e1dd7b2c.
def localCycle00101 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint 41f3406c64ee78d5c1a22031bb6d7a9dbc09522ff41779b29bf98bea502b564d.
def localCycle00102 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 25 0, .triangle 31 2, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 42949d7c8bcc382a765f98cb072e300ea9f13d831d5c17c4e4b4d59db9b32165.
def localCycle00103 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 4, .distance 1 6, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 19 2, .gapLower 1 5, .triangle 18 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0]

-- Cycle fingerprint 4336545a4bb5ebd11157b05ab8c584afa1a8784c802f48ff17e8e9c29eb30b6e.
def localCycle00104 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint 434b88f42fe7dbb4654797a17d589af325c67d217b4b2c43de7a6bb055a745e9.
def localCycle00105 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 18 2, .gapLower 1 3, .triangle 15 2]

-- Cycle fingerprint 44895357066980f36fde9005f7280c02c7485806704659c9010872dfc9f9f5be.
def localCycle00106 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 23 0]

-- Cycle fingerprint 448df974faa3d439b38045ef21dae422072eba09c88373f2ace027a45067f301.
def localCycle00107 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4]
    constant := ![-3, -1, -1, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 24 0, .triangle 33 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint 4827cc05af1f0ae1a24a2f33cbf9b72621c08880ab3a08033f9ee40a501cad08.
def localCycle00108 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![0, -1, -2, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 17 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 48492397819d227504c8ea9d26f1032e94ccc74bc43d5a16994f1f8bc5f07689.
def localCycle00109 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint 48e6734626d952da0a0fd4e1287db0689c7f47de54118b46e80bcabf868de738.
def localCycle00110 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 0, .gapLower 4 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 4a89c7c97e813c715424c4690d8ff6ebee9c45a314ca966efe9d426d24969f30.
def localCycle00111 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 16 1, .triangle 17 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 4b18f8cc92c8f61b2cc31e01146a4afd2ca1554b883a984e126a4e3b8695cd58.
def localCycle00112 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 3 5, .distance 4 5]
    constant := ![-1, 3, 0, 0, -3, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true] }
  origin := ![.corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 21 1, .triangle 20 0, .triangle 31 1]

-- Cycle fingerprint 4b4c015c790f266e80bac5d57692ae7a7250183636597e43ac23e0c10437db6e.
def localCycle00113 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -2, 0, -1, -1, -1, 0, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0]

-- Cycle fingerprint 4b83ee833fb570453d86298d3c43763f54bc50fe1b2e65e208d2fe5b79f31892.
def localCycle00114 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, 0, -1, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 22 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 4c6bf0128be6bd6dafbeea9df099cacfffbf308088572626a39e4f286bb8ca2c.
def localCycle00115 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4]
    constant := ![0, -1, -2, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, true, false, false] }
  origin := ![.triangle 25 2, .triangle 16 0, .gapLower 1 4, .triangle 4 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4]

-- Cycle fingerprint 4d9747cce40cccce6dd1cdb6847951c6a1daef8f5c7ca1e55c7157a3b6d5b786.
def localCycle00116 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 5]
    constant := ![0, -2, -2, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 17 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 2]

-- Cycle fingerprint 4f29f10b1461ffdf0583d9464477a4987dc37ad378a8315e514b21984d87a37d.
def localCycle00117 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 27 1, .triangle 26 0, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4f8cf8ab17969fbf0cde9cdb1804bfc21b9e20a8d8b6516f6c3de0e3b9f81659.
def localCycle00118 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint 50049a39a11dc73249b0d67c763ee42fbdd4a4059b5b4943143ea16e0550609d.
def localCycle00119 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 50391b31f056452a728307c39e475e6aa3a6df8b73ab5d1b1b5dd16c94a89d29.
def localCycle00120 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 50a76d2bb01e85381c09072e5797636937b53d1757e4a01afe5315bb1b9f464a.
def localCycle00121 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 2, .distance 2 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 5, .gapLower 1 4, .gapUpper 2 4]

-- Cycle fingerprint 50ccf8affe96e164b274f1b824b49f81470c70fd310615d87acf3e40d20181f7.
def localCycle00122 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 2, .gapLower 1 4, .triangle 17 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 50f85188dc1d1ff8764651ffc850fa4c19633aa06d66df18acd462646928f48b.
def localCycle00123 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 2, .triangle 21 0, .triangle 33 1, .triangle 26 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 50ff39a545a749802b010675704d52e6640d008e663e343f5ae2598647bc7414.
def localCycle00124 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, -2, -1, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 24 0, .triangle 33 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 518e437ef9366244493ca9b8bd737756a59eb62f3ab63b2b5f561e7e3a8e1965.
def localCycle00125 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 51b578b169d77bd77e394a503bed1936cc55ca1a6fc1d0e043c364e6dfd3224f.
def localCycle00126 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 21 0, .triangle 27 2, .gapUpper 2 5]

-- Cycle fingerprint 5477fcd0ede81eaecca337a0d8b12ba355f6104c3f549c27eef0e1c81536c626.
def localCycle00127 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, -1, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 18 2, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint 553a0730f2d5a52e5899fe10cb6801c379396ef82b0a02b7a1a5714435fdb317.
def localCycle00128 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 16 1, .gapLower 1 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 55564a8d5c22b89b1ca374205393815291d332542eb4cd58ffed6f3307cb8726.
def localCycle00129 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, 3, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 18 2, .gapLower 1 4, .triangle 0 0]

-- Cycle fingerprint 55934910b99eea73eaeefd5b2ed65129696baa6ff551b09723a6da224e3a9129.
def localCycle00130 : Cycle where
  length := 3
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .theta 2]
    constant := ![0, 1, -2]
    coefficient := ![0, 1, -1]
    strict := ![true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapUpper 2 6]

-- Cycle fingerprint 5665f0680b4c18da8e8e80fb05905da9c237343259a8371ef17c7db361a6e497.
def localCycle00131 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0]

-- Cycle fingerprint 57c626e17d69830d6ebfed200412f1fa1f3d2224e8319141260f8b78f6622a32.
def localCycle00132 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 3 4, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![-1, 0, 0, -1, 0, -1, -3, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 25 0, .triangle 32 2, .triangle 33 1, .triangle 20 0, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 57f86b2559540d901a543e316036e853392ddc23843042b32e4c6b2b5e015e3e.
def localCycle00133 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, 0, 0, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 33 1, .triangle 20 0, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint 58c0bf72641e937f6434982edf41c3ee1cd449926058e77bfbd5467fe99c091d.
def localCycle00134 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4]
    constant := ![0, -1, -1, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2]

-- Cycle fingerprint 58e8020f4e3da555e6e05be147f17dab9714d86ddbe513601b725acc2eed1f0a.
def localCycle00135 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -1, -1, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 1 0]

-- Cycle fingerprint 59772f0b4d921709e0f92c6e5243b18dc8003067838595938860906ecc795ad2.
def localCycle00136 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 21 0, .triangle 27 2, .gapUpper 2 5]

-- Cycle fingerprint 5984d6fa43d19e033670444fa0564bf849ca4806eec6a880766877f1afc8465d.
def localCycle00137 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 2, .distance 2 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 59f80d31e201d1d73c27db1b2218fec772355c9cc61533e8a39b94d8432b7d15.
def localCycle00138 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .triangle 17 1, .triangle 15 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 5be5c9339c13c98d3e3d85c15baba458ac5a3fe3d51a3dd446e074ddb0e658e9.
def localCycle00139 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5, .distance 4 5]
    constant := ![-1, 3, 0, 0, -3, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true] }
  origin := ![.corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 18 1, .triangle 17 0, .triangle 28 1]

-- Cycle fingerprint 5c2d655195b4f3011be548e807215faedc557e62daabedd75936d3848221bdef.
def localCycle00140 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 3]
    constant := ![-1, -1, 0, -1, 0, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.triangle 27 0, .triangle 21 0, .gapLower 1 3, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 0]

-- Cycle fingerprint 5c5f31992d733c23ca381660d973decc6636788c5b155f75b6a4271c15453da7.
def localCycle00141 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 5d4c2057678f3f9fa172c433ddae59ca5513b52bf04ec8fbcbf7d1230c504fa5.
def localCycle00142 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint 5d97fa4d46e61e7c5e571f5659ef40cf2678f81fdef0fc2982277a315a7c7c53.
def localCycle00143 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 4, .distance 1 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 21 1, .triangle 20 0, .triangle 10 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 5e48951d5b535ee4878fa9d880a023ed82e94a47f5bbecfb9a90b7b339ab3240.
def localCycle00144 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -3, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 1 4, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 5e760f9e6662264d7c376dea3bfb881ac9f73b1a80bf375603649b0c20cf8a6b.
def localCycle00145 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 1 3, .triangle 15 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 5ee8408e32516f9e3dc55a5d64633e5763c3aebca92f41f2f512d3ac028735d3.
def localCycle00146 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 26 1, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 5f1534a8071e8f9d2a89df4b9c8bdcd606098ab64305d9688ce22441d9cfa0dd.
def localCycle00147 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 5f22717d63be107dae5bbda4d2a4193393aec448c9d8ca8eadfb922e1139e735.
def localCycle00148 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 18 2, .gapLower 1 4, .triangle 17 2, .triangle 20 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 5f2394fba284e064ccfd0ed51b7280915ae36f1a84f01ad71fab2b5e38713e3a.
def localCycle00149 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3, .distance 1 3, .distance 1 4, .distance 1 5]
    constant := ![-1, 0, -1, -1, -1, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true] }
  origin := ![.triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 26 0, .corridorLower 3 5, .corridorUpper 1 3, .triangle 19 2, .triangle 22 2]

-- Cycle fingerprint 5f2a34c03948fcd7f0fa4bb779b090c9450ba3fff4ebb150345ea9adfa2dade3.
def localCycle00150 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 0 6, .distance 0 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4]
    constant := ![-3, 0, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 4 2, .triangle 11 1, .gapLower 3 0, .corridorUpper 2 3, .triangle 25 0, .triangle 19 2]

-- Cycle fingerprint 5f3a509c5c5b39848989c474eb6ee0779e5eb0111b0f6b8652f9df1f0a56d781.
def localCycle00151 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 3, .gapLower 1 4, .gapLower 1 3, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 5f6bf37f160a2a1e37fe37f58d10aa15cd070b7609679a8691d467772e0d209d.
def localCycle00152 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 4, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 5fe643747ad66ead08adda477ade93c7976aaadce7576cbeaeae5dfb389202c0.
def localCycle00153 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 5 5]

-- Cycle fingerprint 602a99182a48bc42bd2b07bfded3c38245b30647d006676f433c3cdafaf8b656.
def localCycle00154 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .triangle 19 1, .triangle 21 0, .triangle 33 1, .triangle 10 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 606f07878008c78de53138b2c5e66e356665e1ea249dddbfa301a6223580e11c.
def localCycle00155 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 1 6]
    constant := ![0, -2, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 18 2]

-- Cycle fingerprint 6091a3a394d934954ed3b0ce8e42dc24f5dd8930bcc8dcb45f347e1b8a54eec8.
def localCycle00156 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![0, -2, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 17 1, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint 60fe0a698a71cfa8e759256fc3a81c82b05a9dff174f1fd6bdc81d2ac6ede3dd.
def localCycle00157 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .corridorLower 1 5, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint 630cf8786dfa976e20f346965b469237c26a09b83a1a1ab0b7ff663f487d1a75.
def localCycle00158 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -1, 0, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .triangle 24 1, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 6371cbe49c11ba2369e5097a4b604be49752f612f6c866489cb164916989a6df.
def localCycle00159 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 2, .distance 1 6]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 18 2]

-- Cycle fingerprint 6492c229033ea2bd3349f7c0d3dcd04b2795b21fc9e901f7f359c169a16ac575.
def localCycle00160 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 0 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5]
    constant := ![0, 0, -1, 3, 0, 0, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true, true, false, true, false] }
  origin := ![.triangle 3 2, .triangle 12 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 2, .gapLower 1 4]

-- Cycle fingerprint 64dc4f0f60d4b930ed14e8ec2b47b44f80d9514a5e62a9c2f2101ce7b7c6d474.
def localCycle00161 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 65de18ae97778e4aeeeefa70ee8ae18c43a4bbd6ff104cc2608c7cb7b18e939f.
def localCycle00162 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint 6703be2f7aba595f5d222ccd53f712e4e29dd7cebb4c123f6811710301d8df44.
def localCycle00163 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .distance 1 3, .distance 3 4, .distance 3 6, .distance 3 5]
    constant := ![-1, 0, 0, -2, 2, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true] }
  origin := ![.triangle 10 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .gapLower 1 6, .triangle 19 0, .triangle 32 2, .triangle 33 1]

-- Cycle fingerprint 671f502bcf286a19931c6a655f026ff9142ea2cca180c491bab79186ca4a1844.
def localCycle00164 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 680c2751dd2fe91a73b09949334e398a1671f14aa2fb33d069de1e363d106990.
def localCycle00165 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 685fcdd70faa84e83c1f1e187b55ec9f06bc61a27ae598f7d16f197f7cf71f15.
def localCycle00166 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 69f53a6c0bb726b925aa6609d91e576bff6d3024822ba5802c11c786d193ac0f.
def localCycle00167 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .gapLower 6 3, .gapLower 1 4, .triangle 20 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint 6a265065f25ec3f962c430f92b22730e978bea8bc2e50bf55dcc9fe6a09ad2e8.
def localCycle00168 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 0 1, .theta 1]
    constant := ![2, 0, -1, -1, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 22 2, .triangle 24 0, .triangle 14 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0]

-- Cycle fingerprint 6a6f9e36f568723fc4bf9f6aa4ac4266117635ca0e0cdbaff163ee523aeca34f.
def localCycle00169 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 6]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 6 5, .triangle 24 0, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint 6c180d07378f87605504491981ec0e10cc5d16473c28befbcfae9804f92a868b.
def localCycle00170 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint 6c5866721fbece920ded5e0d5479ebdfb1502deda1d89717871b8377d15fa485.
def localCycle00171 : Cycle where
  length := 12
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 1 2]
    constant := ![-2, -1, 0, 0, 2, 0, 0, -1, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .gapLower 0 2, .gapUpper 2 1]

-- Cycle fingerprint 6d64c9942f3455139f3cea6cd8a0bffd3f45d01e0757ddc4d313b9a218380c81.
def localCycle00172 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0]

-- Cycle fingerprint 6de41ebe397711c6505c9937b66d58a9e62557b0d694ca8564dbc50163a5fb5f.
def localCycle00173 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 4 5]
    constant := ![-1, 3, 0, 0, -3, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true] }
  origin := ![.corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 21 0, .triangle 32 1, .triangle 34 1]

-- Cycle fingerprint 6dea7ea444f48258e26d9f0bb94f6101c67e9abb8d64c97011e3aa12cc307c15.
def localCycle00174 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2]
    constant := ![0, -2, -1, -1, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 18 2, .gapLower 1 2, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 16 1]

-- Cycle fingerprint 6e362879184b2543283eab5d8dddfea666378684897b58c7de5e6a4c160069d7.
def localCycle00175 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint 6e8c5f99c6f77869148f214811408856f39a2ece2180d7b1e59c399e5a55c466.
def localCycle00176 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 5]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 22 2]

-- Cycle fingerprint 6efba9388469f247680c1ba18a499507dba1d505511b7f4847c0a6b5f7400449.
def localCycle00177 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 3 5, .distance 1 5, .distance 1 3, .distance 1 2]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 5 4, .triangle 20 2, .gapLower 1 3, .triangle 15 1]

-- Cycle fingerprint 71ea96193659485efc3c2cddaea6bad28a9bbe3fc41e7471fedc68847fdb0705.
def localCycle00178 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 2, .distance 2 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 3 2, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 71fbe89b22d9f51c33c26894e2ca9c1b1d0063d1951a60d6b24e99d455ee785a.
def localCycle00179 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 25 0, .triangle 26 0, .corridorLower 3 5]

-- Cycle fingerprint 7277df3bc52ce3ba4fcf1c9e5cd17b8d6dcee7a43ddd21f19821a70bf3a265ae.
def localCycle00180 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint 728c92c0b0eb063b6f51a354165e23c68140ee9371e2ded02837476cdf460433.
def localCycle00181 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 5, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 73e490c7b7ef9a912103b14adcc25307261646c3065e07a23a919260e38f5e66.
def localCycle00182 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 1 2, .distance 1 5, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, 0, -2, 0, -2, 0, -1, 0, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, false, true, false, true, false, false, false, false, true] }
  origin := ![.triangle 16 2, .triangle 23 2, .gapLower 1 4, .triangle 17 2, .gapLower 1 2, .triangle 15 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 7549d5c400d5eac0bb30f0cce2c73326d425ba54a48809fbfa28f424b8918018.
def localCycle00183 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 758b093560ad14dc2fbc18de69cc88cede70996cca66754dfc6730ec8679530e.
def localCycle00184 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 6 5, .triangle 18 0]

-- Cycle fingerprint 75b7cd0080cac80e88a9cebe30b1ab38cdaa67003f15a02e75866d7f9ff0bc37.
def localCycle00185 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 21 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint 75bb79d5ec6a14ec6cae5b6ba397d39df59586c0a04827fc8aa8e2e1baa3ec48.
def localCycle00186 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 763e28b74ff18771d7d821a86d3a7bde3330d28863dabd43b8479559a5d49dc2.
def localCycle00187 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5]
    constant := ![-1, 0, 0, 0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 22 2, .triangle 24 0, .triangle 34 0]

-- Cycle fingerprint 76bbb4e2775917cd49c3f77548c28097235cfebf42dc1e2033b129aba49ddcb0.
def localCycle00188 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 3, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 76ddc530ab041e69d6687f346e7d2950b4d38753642b41f3c5f028cd56f58ef0.
def localCycle00189 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 33 1, .triangle 20 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 76e86397bd300bae259655bf87ae1c90888a13a1ddfe8d614c6965b176921b6a.
def localCycle00190 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, -2, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 21 0, .triangle 33 1, .triangle 10 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 77f62b8c45e539414f35543cdc11ef579cebfb20b149e3971c10af27e0990065.
def localCycle00191 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 4, .triangle 18 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 78306d74b338021e1022cbfffe8596bfee93a874674c8ebfaced25ea6e6948e7.
def localCycle00192 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5]
    constant := ![-1, 0, 0, 0, 1, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 22 2, .triangle 24 0, .triangle 34 0]

-- Cycle fingerprint 783e2b4add81bcb2d13abf40f690ac662e5fef18a2cd1c57941f7f666c7df84b.
def localCycle00193 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 787daae483500008454fdb5cc94bde0d17d2dd6568984d2ef1386c1091bb9e37.
def localCycle00194 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 2 6, .distance 3 6]
    constant := ![0, -1, 3, 0, -2, -2, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true] }
  origin := ![.triangle 33 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 18 0, .triangle 27 1]

-- Cycle fingerprint 789c45ab4e003b5e4a1362770afc9db882c07f72aa038c6c61564b30dcf21ff1.
def localCycle00195 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 795f75f8587fbe5561d1550db728531169ab5e9105a31b84abb3d8a23ced9a4e.
def localCycle00196 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 799fe6b50e3c4c1202ec63f00cebf4b58ff95205617736ac307b4843fa6c9e1a.
def localCycle00197 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 1 5, .distance 0 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 18 2, .gapLower 1 3, .triangle 3 2, .triangle 12 1, .corridorLower 4 5]

-- Cycle fingerprint 79a1410eedb1a38bdb16973276c854616ae399911bb90829cadbd96dfb48e1ea.
def localCycle00198 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 3 5]
    constant := ![-1, 3, 0, 0, -2, -2, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 24 1, .triangle 33 0]

-- Cycle fingerprint 7a4aee3c1865bb4249b7973deeb9ba54af9e3d8f552fa400f6a3d846b91c32d5.
def localCycle00199 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 2 5]
    constant := ![-1, -3, -1, 0, 0, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 30 1]

-- Cycle fingerprint 7a7709eb796caf3552a3092315cfb93f80c3bb6368ef62a3ecd2565318ccd6bc.
def localCycle00200 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 3 5, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, 0, 0, -2, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 33 1, .gapLower 5 3, .gapLower 1 3, .triangle 15 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 7aa83b4615ce9820b6bf87a5135abde523ad153f74d268bc9674288525469778.
def localCycle00201 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 7b23bd103d500c17f827e1d953853adad4e83668b30b26e5e80c888f93e6a641.
def localCycle00202 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, -1, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .gapLower 6 3, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 7c484e4c9be6369cea851b3805679b26c8b708295639f00d9964d31fad7e91bb.
def localCycle00203 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -2, 0, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 21 2, .triangle 24 1, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 7c809b178a96e6558457d75a4e650a0bfedce7b0e5827433670f336db9d96a40.
def localCycle00204 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 5, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 2, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint 7cdab0d8f5c55b28eb1d79a1571e9f2d5f5115833d38403e00712344800beb93.
def localCycle00205 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .triangle 19 2, .gapLower 1 4, .triangle 24 1, .triangle 17 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 7dd8236cd31226ebbad644d511d485e3c84979e589594cf11ebd49f47665cdcf.
def localCycle00206 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 7de15d6de6c703ebea1261894f6aab40e86a7389e9d0d318655bfef40820fddf.
def localCycle00207 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5]
    constant := ![0, -1, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, false] }
  origin := ![.triangle 26 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 18 1, .triangle 17 0]

-- Cycle fingerprint 7e2076cad34f2079c89af3fefbc6f194fbb349628e40483cb6f47517cd9dff76.
def localCycle00208 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 1 5]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 7e243d04fe835e8fab2662693f27a34f052d337120e445302aa900f4caa4d0d7.
def localCycle00209 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 3]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .triangle 24 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3]

-- Cycle fingerprint 7f8cad7a0c006cd971792e0ae120aa147d786e7a48d2e1cd0f372b0456ba075d.
def localCycle00210 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 1 3]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 2 2, .gapLower 5 4, .triangle 20 0]

-- Cycle fingerprint 80c054f41a5aab00d08d0f06849060b558b82ea9c5985f4a06536de154c77995.
def localCycle00211 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .triangle 18 2, .gapLower 1 3, .triangle 15 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 82b9ba9495b268d85010da11849e219c29532b90c6ff4a6fd80d857e34911334.
def localCycle00212 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6]
    constant := ![0, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 2]

-- Cycle fingerprint 832fb2a45cdb7687a08be5caa878c552d8dde07177f180588cd52d009f147f3e.
def localCycle00213 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -1, 0, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 18 1, .triangle 17 0, .triangle 26 1, .triangle 5 0, .triangle 0 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 83c40cea4fd543ef580bc359a226ababf9116075ad483c78d019e061b07c9d9f.
def localCycle00214 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint 83d3184bd2dff112cb402d98372e1b533ca9661d877963c4825ca62ae46823cd.
def localCycle00215 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 83edf49cb68bfd23d058df45705941b3bdb10c7008f83d0548d4d3ea420216ea.
def localCycle00216 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 2 3, .distance 3 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 27 1, .triangle 25 0, .triangle 9 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 84730b3ef4ffe134d5401be22ad5f1c5cfff72b4a22361885ac3bcbe76b5f6f6.
def localCycle00217 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 84cb98fceaed0995746b442e538f9e44c030bc32a41a57d217531e9f52cb6020.
def localCycle00218 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 84dbd38d61fc03413c7160d159f37e8710f21e5f47cdb1de76142dbd91d4d8cd.
def localCycle00219 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .triangle 18 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 855250c37c20b5f38102d4507362407cce51733deb044b96ad849fd82dd7dd5d.
def localCycle00220 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 2 5, .distance 0 2]
    constant := ![0, -3, 0, 0, 3, -1, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .gapLower 2 1]

-- Cycle fingerprint 864796e1e1359bf6550f0a21904eaf943591ceb6d0898ddabc75c623b7806578.
def localCycle00221 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 8671a6d07e97431c718efee40d5b8202b7f977b9ab9dea5bb44e424b54456331.
def localCycle00222 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6]
    constant := ![3, -1, -1, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint 869886e3df8c77a2e6ff34bfa15581dfc534a74302c2bfebbb6fffb67c49c205.
def localCycle00223 : Cycle where
  length := 7
  data := {
    node := ![.distance 2 5, .distance 3 5, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 2 5]
    constant := ![0, -1, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 26 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 2, .triangle 17 1]

-- Cycle fingerprint 86dbe340c6b6ae3b3540d6bb4e8ec0e3ffbf68d9543585a0df91fd214d579520.
def localCycle00224 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 0 0]

-- Cycle fingerprint 8826069bc41f788bffc10f25ee2bbac7a002fdf2028fea2fabf7d4885c64dbf8.
def localCycle00225 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 896652bce437f97d4ad5fa61e67f31d4611b69c091d8eabb1eb8ae25960dacfe.
def localCycle00226 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 25 0, .gapLower 2 1, .triangle 0 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 8a587f70b50aab7a367bdfd1e9f51c2ffcdede6c0a450a5b5508e8cf20fbdcf4.
def localCycle00227 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .gapLower 4 0, .thetaNext 3]

-- Cycle fingerprint 8a7072d912d64296c76ed1dc7db5df50e19dbfa9a3f26e6145d7f2bbee6a459e.
def localCycle00228 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4]
    constant := ![-3, -1, -1, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 24 0, .triangle 34 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2]

-- Cycle fingerprint 8a90cc1e6e2e38ce331da101c6d5b73a994453868563eeb8b8467b4e6f213d53.
def localCycle00229 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, -1, 0, 0, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .gapLower 4 4, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint 8aaa6095975f36095b3de42713356003a791a260090f966c2f5299ef17c6f22f.
def localCycle00230 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 8ab759b426a3e7803bfaada12603ffdeb6210275a12e69a3f9eb0771bb4ba9d1.
def localCycle00231 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 1 3, .distance 2 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 8b81a1f8a5ac33de67657f2a3c9b2df6e61cc9b3ca5a2bf9a771587733baf0d2.
def localCycle00232 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint 8ba5af77d375a0fe1f71ad65f83be622ef1d5b896f5a14f68e0ebf9ee0a50eb8.
def localCycle00233 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 0, .triangle 32 1, .gapLower 4 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 8c97446fbf6816699186a1a135ccddae118488799168def45401b2caa20a77bf.
def localCycle00234 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![0, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 22 2, .triangle 24 2, .gapLower 1 2, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint 8caa566e6e62adaf3c1f9bb6124029d99d9e73cc8e91c5943ff2545ac0827c9d.
def localCycle00235 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 8ccdb354866ee0494b71e93ea98708a3e3478d557f0f865c98d8f2870c386290.
def localCycle00236 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint 8d02ad5aaebca26cc8e73386310712e82e388c0cf44272952c739993fd0af98c.
def localCycle00237 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .distance 1 4, .distance 1 3, .distance 3 6, .distance 3 5]
    constant := ![-1, 0, 0, -2, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.triangle 10 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .gapLower 1 6, .triangle 19 1, .triangle 21 0, .triangle 33 1]

-- Cycle fingerprint 8d8d26605ab27b18bf3346f43aaa631abd34c33d9e3fa0ec529ab9862678d84b.
def localCycle00238 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 4, .distance 0 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, 0, 0, 1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 2 2, .triangle 13 0, .triangle 34 1]

-- Cycle fingerprint 8db15a8e06d56b462dc663d1d55d7ec904ce70d5b959f576036d7d092384330a.
def localCycle00239 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 8dbb98e1d739bf633202951057ce92e3e365d034df19b08062f1999735a239eb.
def localCycle00240 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 18 2, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0]

-- Cycle fingerprint 8e3abcf5842f9357f363915860a2c7c01526e24b4003b5232a6e573f733e5196.
def localCycle00241 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 6, .distance 3 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4, .distance 1 2, .distance 2 6, .distance 3 6]
    constant := ![0, 0, 0, -1, 0, 0, 2, -2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 33 1, .gapLower 3 1, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 16 1, .triangle 18 0, .triangle 27 1]

-- Cycle fingerprint 8e530950249fd7b8c9e3296a14ff730eddda42ca653a4466decc11734e5dc794.
def localCycle00242 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 5, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 1 2, .triangle 17 1]

-- Cycle fingerprint 9009b0a53f6a19d8e0b939d8f0994d100b38d4da6e5d89643e71df8195f6e4d7.
def localCycle00243 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 0 5]
    constant := ![0, -1, 3, 0, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true] }
  origin := ![.triangle 12 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 3, .triangle 3 2]

-- Cycle fingerprint 9135afafdb6f4a3d4f17c4098390a49edf0e1eda846886c839a84de466278477.
def localCycle00244 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .gapLower 4 4, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint 91665d6801168d5eb12b18a33b4949b8e471f2cafb85040071b347a796a9fd98.
def localCycle00245 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1]

-- Cycle fingerprint 91675553f08df58c66e78dd48e6c462a85367ef7cc2105c9712033a56667ded6.
def localCycle00246 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 9263c9d7bac6641604312369369f7efba17f2aaf6733fbbd0ed81ec8bd7e362a.
def localCycle00247 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 940fececf62801a5104d061eb246fa0add861553a0abcc72f2986f8b9fddda6b.
def localCycle00248 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![0, -1, -1, -1, 0, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 9449d5624757fbb836dc121971b8c03c9b3cd8eb7ea5d54d6e439c489c0a44d3.
def localCycle00249 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6]
    constant := ![3, -1, -1, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint 95d67239f08f5b0659a31cb606e706d941926e9537c12b18b471a55ba3d8b1bc.
def localCycle00250 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 968dfa9d10f961a9f0046706a28fbeac28978f1ddbc35463622efda303289e18.
def localCycle00251 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 1 5, .distance 1 3, .distance 3 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint 97038eea04441670f91e88eb7f3a9ae5eb5285c159e22dc4bcaef419332937c3.
def localCycle00252 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, -1, -1, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 97150b42460e273a2807962a16914b6f34cc702ff361e8eaf6ef2719966a72c6.
def localCycle00253 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![-2, -1, -1, -1, 0, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 24 0, .triangle 33 0, .triangle 10 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint 973f6d567d1135534acc13122e39fc4e2ec7a818389483a5accb50657177f304.
def localCycle00254 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 15 2]

-- Cycle fingerprint 97519165366540dab8c061ffbdbbdf695df9637ce750624c70e002664a26d672.
def localCycle00255 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-1, -1, 0, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 15 0, .triangle 5 0, .gapLower 0 1, .gapLower 1 0, .gapLower 1 6, .triangle 22 2, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 9776a3a6e1297caaa9d934d782bc3a7a5dd0c22a359667846fea6ab6b50c5fb2.
def localCycle00256 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 97820f4e3286331e9c2cc0ec7fba136ef82e3eafe79d070cc5832694b45dccd8.
def localCycle00257 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 1 5]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 2 2, .gapLower 6 5, .triangle 24 0]

-- Cycle fingerprint 985cd8c2f2d93e1851058bd5b16ca9e3f9909f1fa5f2b0b0d9c050fd202b0971.
def localCycle00258 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 2, .distance 2 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 3, .gapLower 1 4, .gapUpper 2 4]

-- Cycle fingerprint 98cdaeebdb6ff6b0dbfb0097769dae225af628f414869568d6de022d3c51c7cc.
def localCycle00259 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 98e76b9fc5a0dc26a5916ef54198df39bb27dd9763d877b2e69962582736ef03.
def localCycle00260 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 9a05ec3c9c4b75c5623b2a8fe0b34fc48c934105ff6c50d481e085ca51103f12.
def localCycle00261 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint 9a7ebf9198555754c79c448cf2236a3cf9461bfb1ff6234e38c6358fb53786d5.
def localCycle00262 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![-1, -1, 3, 0, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 33 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 22 2, .gapLower 1 3, .triangle 24 1]

-- Cycle fingerprint 9b828e6cab49028ce84e20f9369d7465fa98b665f9226d466b11a8d0e41cf76b.
def localCycle00263 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 1 3, .distance 3 6, .theta 6, .theta 5, .distance 3 5, .distance 2 5]
    constant := ![0, -2, -2, 0, 2, -2, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, -1, 0, 1, 0]
    strict := ![true, false, false, true, true, true, true, false, true] }
  origin := ![.triangle 17 2, .gapLower 1 4, .gapLower 1 3, .triangle 15 2, .gapUpper 3 3, .gapUpper 6 6, .thetaNext 5, .corridorUpper 3 5, .triangle 26 2]

-- Cycle fingerprint 9c2f527a6c07a067310b6488c0d594eb62d5500b77a8cae446d8d2f8e65192d5.
def localCycle00264 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 9ce3b3a0ee41a5e716087698854f5fa40d709a509b310516c75d9bea6c8fd602.
def localCycle00265 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5, .distance 4 5]
    constant := ![-1, 3, 0, 0, -2, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 17 0, .triangle 28 1]

-- Cycle fingerprint 9d3e2d5289cc53da5906bdf002a04d259157584292927e652ac4073398f30254.
def localCycle00266 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5]
    constant := ![0, -1, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 26 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 17 0]

-- Cycle fingerprint 9e01c433c933ed38db08ced3f49390ba586a8842ed01a70aebd148a3be13cb94.
def localCycle00267 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 2, .distance 2 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 4, .gapLower 1 5, .gapUpper 2 5]

-- Cycle fingerprint 9f5af8f586b7e6b0122a506dd87a70aff5a9f77dfe5f78715eecca094fd8e3e4.
def localCycle00268 : Cycle where
  length := 12
  data := {
    node := ![.distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6]
    constant := ![-1, -1, 0, 0, -3, 0, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, true, true, false] }
  origin := ![.triangle 33 0, .triangle 10 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0]

-- Cycle fingerprint 9fe633bb1610c334355bc2d9cbd89bf49344d50f13a163ed4fedca86e04b6779.
def localCycle00269 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 2, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .gapLower 0 2, .triangle 0 1]

-- Cycle fingerprint a0c1496baa8582c59383e4c0df87d2a6485f28899fcdbab86f216d475e9d631b.
def localCycle00270 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint a171447624e5be71d020eb7b4ee3e49b57849fc5a19a0547b5d19c7b78747ede.
def localCycle00271 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 20 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a179fcb82e3433ac48064bfe3e554b8eefce5484667951b2620289758fc13bd4.
def localCycle00272 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint a4aa11701ca64cd97fc33782c0c8bdd826223e85709c4afd3b467ab2f08cca85.
def localCycle00273 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 32 1, .triangle 25 0, .triangle 26 0, .corridorLower 3 5]

-- Cycle fingerprint a4f92db99d01c5f146eaab8c359a0b784a756fbd14285d5de880895032cc05cb.
def localCycle00274 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5]
    constant := ![0, -3, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0]

-- Cycle fingerprint a533fa77a13e614128c213680052bd1eb8605d0bbbdda6d0419bcc66a17977c0.
def localCycle00275 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, -1, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 1 0]

-- Cycle fingerprint a54b782b9cf4a9956c12ef283798793e316bd0156e7d5585367707380e84707c.
def localCycle00276 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint a6165616cf8f0194b3d2cc699303f5c3daa1b60a1ec2fb5dc1219f9ca9765c69.
def localCycle00277 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, 0, -2, 0, 0, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .gapLower 4 4, .gapLower 1 5, .triangle 24 1, .triangle 20 1, .triangle 15 1, .triangle 0 0]

-- Cycle fingerprint a77718cb5c484f5903d8a1981aae50656a247eea736626e85b7c977cd2db0fd4.
def localCycle00278 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 0, .gapLower 1 4, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint a80a3de1882061dd788011eefa85d0b06f8385eb3a6d5923a8c191884d25e653.
def localCycle00279 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .triangle 17 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint a818172455b17eca3ca44a1aa9e81cc23ad0affa75668577cd0b240baa58f869.
def localCycle00280 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 4 4, .gapLower 1 5, .gapLower 1 4, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0]

-- Cycle fingerprint a8cfeac4caf644fad40e2e5f1ae2726d1e91e45568df9cebdd6e062e41d69f1b.
def localCycle00281 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4]
    constant := ![-2, -1, -1, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 24 0, .triangle 34 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2]

-- Cycle fingerprint a99f630409cbba976970166355134bfe95cd49017510cfdad53a6a11786b9cc0.
def localCycle00282 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 3 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, 0, 0, 2, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 19 0, .triangle 32 0, .triangle 34 1]

-- Cycle fingerprint aa5d8fc73799c4f6f43937a126a31f7ed78df362071661fecbbc35838eb60c34.
def localCycle00283 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 3, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint aaa066eb6d5d830b33f5844988bd0735e5f639a755e69f70d6fd4d4d5b923466.
def localCycle00284 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint ab18c40d4cb6e2eaaaca33ecd6603fa6da4386d36ec65f465d4ec3ca945e2d37.
def localCycle00285 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint abf4e6aaa081becc089bfbf7b567f10d5e2e819c7a38342129efe7bd1ef01cfb.
def localCycle00286 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint acc43247be474436ce2e3bdc77d8e024a51a708e4b3f5d6d1b407fda60945683.
def localCycle00287 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4]
    constant := ![-1, -1, 0, 0, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 25 0, .triangle 5 0, .gapLower 0 1, .gapLower 1 0, .gapLower 1 6, .triangle 15 2, .triangle 21 0, .triangle 32 1]

-- Cycle fingerprint acfa68c92fe2451479c98e59bbf2928b7ac071983fd1546f51aa93a0ef1c5eac.
def localCycle00288 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2]
    constant := ![-1, -3, 0, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0]

-- Cycle fingerprint ae4af1835d651df2a88d86558e93d9ecfbece4f2de15da155454f16b76deee0f.
def localCycle00289 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 2, .distance 1 5]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint af53df9d225e34764582d21f9e3a2b5d9f03dc19ddba02bf2c1dca563ceef19f.
def localCycle00290 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .triangle 21 1, .triangle 20 0, .triangle 26 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint b04f30e924796800b762ca0f6ef99f8445917e0b8da037e22c23345cc52cdc3b.
def localCycle00291 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint b07055bc5b95ab4573d624079d4589696e4b0b17d7769c10c3b5cb9c72074398.
def localCycle00292 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 3, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0]

-- Cycle fingerprint b09bc96bb6ceae67d0883c761191b4ddcb349e68bb620a7d76627f99d51463de.
def localCycle00293 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint b0a9c85a3c5b2f98757c8dc26868cfc9aa8cd2f2733c2b4839a5f118fdb84b19.
def localCycle00294 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 4 5]
    constant := ![-1, 3, 0, 0, -2, -2, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 24 1, .triangle 34 0]

-- Cycle fingerprint b0b12b393ac63663242bbcb75a4feab9fad278c8e3d63b97e7c57876ccc4aadb.
def localCycle00295 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -1, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .triangle 24 1, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint b0c92ec97c3c9a3fdc3a3ccd1f74e10c67b7ca8aeee6a6568d557f8d09a72334.
def localCycle00296 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 18 1]

-- Cycle fingerprint b120b8c51174234f0e78d8578060ae63a028f1b2dafc4ab26411dd7d28c29527.
def localCycle00297 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4]
    constant := ![-1, 0, 0, 0, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.triangle 25 0, .gapLower 2 1, .gapLower 0 1, .gapLower 1 0, .gapLower 1 6, .gapLower 1 5, .triangle 21 0, .triangle 32 1]

-- Cycle fingerprint b133a6e25b4ae7a2866a921f0263ec8a301806ed16cad43d6698121f7c89b7eb.
def localCycle00298 : Cycle where
  length := 7
  data := {
    node := ![.distance 2 6, .distance 3 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![0, 0, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true] }
  origin := ![.triangle 27 1, .triangle 33 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint b15b72f8189075089648677e021057b43a8e75bb6484be7d3ba2b7b4337bd8a7.
def localCycle00299 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0]

-- Cycle fingerprint b25d11bca8303199b723fcc092e82234f7dc78294a173b949d2c56e15fb658ee.
def localCycle00300 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, 0, 0, -1, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 33 1, .triangle 20 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint b296906f5e4273d2835b3d50f5c47a35782bfdd1b7c0ace9f8a0de6c1684a1da.
def localCycle00301 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint b2adc7710e25403ba685114b7712c0e8aecb1d67c80a1411cb18de83b2d8f7f8.
def localCycle00302 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 16 0, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint b2b6266edb92e2a2af1b577c008da24c28807ae113fe5db1dc75d93b186e958f.
def localCycle00303 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint b34cfb258bc4b3b905e856b1398f38efd94f4c24081476c0be74fde84e8be09e.
def localCycle00304 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .theta 1, .distance 1 4, .distance 1 5]
    constant := ![-1, 2, -2]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.corridorLower 1 5, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint b5d0a64c07e084aea9880e039b347d1428256ab36fc09d25e99479c274219526.
def localCycle00305 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint b5e714b1c73b8428f1f08cf7539810e71936207d9eb90158632d758fca3a6b44.
def localCycle00306 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 4]
    constant := ![3, 0, 0, 0, -2, -1, -1, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 1 4, .triangle 20 0, .triangle 10 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint b6603c48ac9eac8a755620596a04c29fb1b853b4a3d145082f43d3064414f811.
def localCycle00307 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 5, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint b76f84521ac68ecfe4d9e3f851ffae69e215ebf00bd805f49893fb970a55571e.
def localCycle00308 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint b894b24f568af6beddc1339d05bc1f661c7647dde876710e7b6fad212ccdd762.
def localCycle00309 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint b8ab496e2beddf06491f279beab35659ef6ab3c9a4aded092c371a39d3d58483.
def localCycle00310 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 26 1, .gapLower 2 1, .triangle 0 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint b8add20e989d34c73c657c58bb3f27c3e01ac2e44fa82b739fffd54296678248.
def localCycle00311 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint b9c29007a7a164d16f5b0aa64d3d635e58dbd422c95a190600cc8e79414c5feb.
def localCycle00312 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint b9cf5d1879edc7d3cd6b1236e9911fdadf75e9d03bc247e26e7ee1489c7c33b5.
def localCycle00313 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 2]
    constant := ![-1, 0, -1, 0, 1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 1]

-- Cycle fingerprint badf99e119b98bf2b4c8ae41dce568fd18dee2232f108e0f97286b9f7a0448ce.
def localCycle00314 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, 0, 0, -2, 0, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .gapLower 6 3, .gapLower 1 4, .triangle 20 1, .triangle 15 1, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint bbd39cc5d8f88b8395c699f46c3f7a8f271a2704e5d83ec925e1c8cd3baa3a41.
def localCycle00315 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 5, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 5]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 5 4, .triangle 20 0, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint bcb4186d15bfcf98df4c66d7240997b5a56d9a79501f7a4ce8eec2ec83400839.
def localCycle00316 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![0, -2, 0, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 21 2, .gapLower 1 3, .triangle 17 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint bf3ce67ab7df63f40e52956ffc01d132df0905011b4852d7f7427691b3f7a04b.
def localCycle00317 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint bf4f646a0fb5750a5a59ecbdbea96c39298fb1b9951decd69607f46b0753cf77.
def localCycle00318 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2]

-- Cycle fingerprint bfa93dfe729ca333ff429985f1e66b251bf357115fb8bf9ef1d9cec70a9d8e85.
def localCycle00319 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 30 0, .triangle 7 2, .triangle 12 1, .corridorLower 4 5]

-- Cycle fingerprint c01afb07aa35b287026f5a3945cf6a1f785165c4886127aff655c2900dc5efdb.
def localCycle00320 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint c25a2b7318a16060a079731494cd7ed4487639d09f0f1db8332827fd1458008c.
def localCycle00321 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 4, .gapLower 1 3, .triangle 17 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint c2cb2403d95d7312570f9c7a909cec66abba02da28a1b04dd9a3c0eaac014c7e.
def localCycle00322 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 4, .distance 1 6, .distance 1 2, .theta 1]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 23 2, .gapLower 1 4, .corridorLower 1 2]

-- Cycle fingerprint c2dedc4d6c796215fc083589462166de5526900333910fb922fb557785e0093c.
def localCycle00323 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint c3ae41357667c62c5beffdf56fba555c5faf547f45d97a40a2c9c5047ad22574.
def localCycle00324 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint c3c44b86ec30a1f70207fb4b3ebb1648230169da54169745ca1ec93c4761a636.
def localCycle00325 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 4, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 1 5, .triangle 19 1]

-- Cycle fingerprint c3fd8164e987bddffd4f595c33ea128ea21e13f7ce778fde9a501d59602220e5.
def localCycle00326 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6]
    constant := ![-1, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint c4db3e0430c3bd7ecd52bcc5d0610f0aa21ac0930f8febc36a8ea47c42c6bdc6.
def localCycle00327 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint c528d36d14bfc2e61e9669d0669eb20259dba48cf8c1debfaae8780382226d2d.
def localCycle00328 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .gapLower 4 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint c54ddd8ff40bc848551e1ee92b9f43d21fd4c8c43d6a7751e104c52d7f919b11.
def localCycle00329 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6]
    constant := ![0, 0, -2, -1, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 23 2]

-- Cycle fingerprint c5fcfee85447095ca6307e251d8936a1182e055f305628a1a4a6fdbc373cd6a9.
def localCycle00330 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2]
    constant := ![0, 0, -2, -1, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 18 2, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 16 1]

-- Cycle fingerprint c640849dcc36685d080b3e41e2e4b341a30db88837ce48550ea16140f27f637a.
def localCycle00331 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 22 2, .gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2]

-- Cycle fingerprint c66bdfaf8f4775a293fc8369ad27dc329d9e47e01fb7b3fde1d61da18f00faa7.
def localCycle00332 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5, .distance 3 5, .distance 2 3]
    constant := ![-1, 3, 0, 0, -2, -2, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 1 3, .gapLower 1 2, .triangle 20 1, .triangle 26 0]

-- Cycle fingerprint c66c95489fbdc596839ff4d3f5c4df784ba2547b8260cbf8f0f25f8d9a4d4a4e.
def localCycle00333 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2]
    constant := ![0, -1, 0, 0, 3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 18 0, .gapLower 1 3, .triangle 20 0, .triangle 26 0, .triangle 5 0]

-- Cycle fingerprint c95d941a5235f29894c1c86134571957076074e1d8257154d38f650a479de4ed.
def localCycle00334 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 18 1, .triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint c979e848d55dd83925d29c3e0630509ac7a732469f22e0cfdf41712442bc36e2.
def localCycle00335 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 3, .triangle 22 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint c9d27ef1693da5337356923fa0b484c5a88d48c08de6cdd8b98a5cc9139d77b2.
def localCycle00336 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -2, 0, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 18 2, .triangle 24 1, .triangle 20 1, .gapLower 1 1]

-- Cycle fingerprint ca549de2c8bd1ce05084dc2d3aeac9d060c95cd535042a4c44c1be0734300148.
def localCycle00337 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint cc661757948d3264df9a0d99750e4a5bbf1a56ebd7fedd333428c92b7fd7246c.
def localCycle00338 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 18 0]

-- Cycle fingerprint cd9c75a71d03ef2ceaf2a2e7f4c5d81e808418da7719e8b6f3aec928b5b36768.
def localCycle00339 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint cdcf6b5468840e44d80e952e01fce94f9efd67ec4031efd6dafa440012892891.
def localCycle00340 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 2 5, .distance 3 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![0, -1, 0, -1, 0, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 16 1, .triangle 17 0, .triangle 26 1, .triangle 10 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint d2eda2961e6b837c8bc631cb2b250b485e842aec67fb191c54f05e1afb8cd421.
def localCycle00341 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 1 5]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 17 2]

-- Cycle fingerprint d3495387c7f8517c77914a65f4fe62254936423ffa3b3e118f6bc15a9ca16f8e.
def localCycle00342 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 1 4, .distance 1 6]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 3, .corridorLower 1 3, .gapLower 1 6, .triangle 23 2]

-- Cycle fingerprint d3d110902b8e270adfa7f2df7ecad1da4974d14c8ff1c227d652831a82dd68db.
def localCycle00343 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 2, 0, -1, -1, -1, 3, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 22 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 2]

-- Cycle fingerprint d4b16e551737c7fc0e8ad7597ae92517452092b2d30e683da9d8dcf5c9bcf909.
def localCycle00344 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, -1, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .triangle 24 1, .gapLower 1 2]

-- Cycle fingerprint d4d9727772551381b138fe0483b14b7b3d72af96192bb07cebc4ed24e742d97f.
def localCycle00345 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-1, -2, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint d5a989a0aed197970196e7b3990b5da169a3ddb817203fc6c619d7b1994d1f3a.
def localCycle00346 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 2, .theta 1, .distance 1 4, .distance 1 5]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .corridorLower 1 2, .gapLower 1 6, .triangle 22 2]

-- Cycle fingerprint d7931389e17c9d43bffce3a8910c86c057142abee0570370220cce04a3d09979.
def localCycle00347 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint d7accbd121f9b059fe48e2791b78b51af55af5ed72cc8146268cbbaf61260807.
def localCycle00348 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 6, .distance 3 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4, .distance 1 2, .distance 2 6, .distance 3 6]
    constant := ![0, 0, 0, -1, 0, 0, 2, 0, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 33 1, .gapLower 3 1, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 19 2, .gapLower 1 4, .triangle 18 0, .triangle 27 1]

-- Cycle fingerprint d8493897b9ace056094350707747895c88e03954cc3b5fd38206a8dea2bcb8ae.
def localCycle00349 : Cycle where
  length := 13
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, 0, -2, 0, -1, -1, 0, 0, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 24 1, .triangle 33 0, .triangle 10 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint d8d6d3670ec9de826e1e2c9e0c2ab0d647fc7f04911ab4bb63c254de8014cbbb.
def localCycle00350 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 17 2, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0]

-- Cycle fingerprint d9b490ae15c4ed10c80dd06853f04da26db025438d3d00ccd3f5e1e3bf4571f8.
def localCycle00351 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint db18484c8fffe4ba573419e0e735c11c24b409ad80ce01d435914f4db17f0c3f.
def localCycle00352 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 0 0]

-- Cycle fingerprint db55541d4ac56078e3cb012029561c24178d970e80335890b5d45632e2b12e01.
def localCycle00353 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint dbd70184b9cd5fc44fbd3f55b5c7c7c64f33cbf7efe4bc239a16f0016df242ee.
def localCycle00354 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5]
    constant := ![-1, 3, 0, 0, -3, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true] }
  origin := ![.corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 18 1, .triangle 17 0, .triangle 26 1]

-- Cycle fingerprint dc330d0e26d27779d31d5fe8f622719b7db9ca2f63a0072a6d953d16003fa4b3.
def localCycle00355 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -2, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 18 2, .triangle 24 1, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint dcbc905b821bdbf1e3ee59a6197620aefc60afb406d6384270367c6e432587bf.
def localCycle00356 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 1, .distance 1 4, .distance 1 2]
    constant := ![-1, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint dd6e9eae4035d02cd2001fd36658a9c57791504f69625de100484ecebc117f3b.
def localCycle00357 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint de9705649ececdd5de7e38d50eb968a38e39c00a122522fc8984072ab0ca148e.
def localCycle00358 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -2, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 21 2, .triangle 24 1, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint df8e0b16f5ceea806f8a8167bb403ce39d85c8a95b81a6477c2f537b817e2538.
def localCycle00359 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 0, .gapLower 1 3, .triangle 20 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint dfa122b36a577155cf70945ceec1eb16b07acbd739a63f06fd903797cd6d1b40.
def localCycle00360 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 3 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, 0, 0, 1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 19 0, .triangle 32 0, .triangle 34 1]

-- Cycle fingerprint e027c66b2b5dc3c677d37756712b679e1e772590c2ec89c44d5d13cc0c2d07c7.
def localCycle00361 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4]
    constant := ![0, 0, -1, -1, 0, -1, -3, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 1 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint e031c7daa302223b6e911ab67c86db8e30dbb847d2227016d791777fa712783e.
def localCycle00362 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint e051f896aa8f44857f159acae3a12efde33ace98ac42865456ab66f0cecfecb4.
def localCycle00363 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, 0, -1, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 21 0, .triangle 33 1, .triangle 10 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint e0b4729b038b98a15d003c08194891909175a7a886c524086e9c9625c142c043.
def localCycle00364 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, -1, -1, 0, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, true, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .triangle 20 1, .triangle 15 1, .triangle 0 0]

-- Cycle fingerprint e1212cba1de0320fd65a6ed62a1bea073ff44624fd3b3b922be11412c8146a45.
def localCycle00365 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0]

-- Cycle fingerprint e1a68970e4bad34ec968816c9dc32817f7edd74936d94e4ea9ecc213420cdca1.
def localCycle00366 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint e343d47f4374fb700efb0043cb0da89362ae755879ac9022186f0178a258fc78.
def localCycle00367 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint e40ae0c84a705b3ea219c3432df57438f0b27f12ccfa25a999241eaa9fa78e01.
def localCycle00368 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint e45284e84e6651fec95ba65fc7d9e2596564aa0ae69f2bea1bbdf9907218e1e4.
def localCycle00369 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4]
    constant := ![-2, -1, -1, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 24 0, .triangle 33 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint e453da6aa5fccb9e97f3eab0541e1bc95a9d759528a958d3d3ed808485a8e6d5.
def localCycle00370 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 0, 3, 0, -1, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint e46c218b1a8272ef55eca8bf7a5ad33846462d5283c48ba3c57069063b5bd964.
def localCycle00371 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 5]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 18 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint e47848a6a1f97dbec2fc884e49c1e951ceb92634ad8f5dbb7c5e35f3cf3da05a.
def localCycle00372 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 2, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint e548f077e858307e81a64454f7c15f6ba221b492de1eee96f26d56c852447f0b.
def localCycle00373 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 6, .theta 1, .distance 1 4, .distance 1 6]
    constant := ![-1, 2, -2]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.corridorLower 1 6, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint e679aeb0775d359346b4ac1f117e5724cc5508a57d31ac106cfd1c08f59cda8c.
def localCycle00374 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint e7b151478515786012f5af6607e3172bb7580aa1bcf28527788dac7d22f75af5.
def localCycle00375 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1]
    constant := ![2, 0, -1, -1, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 19 1, .triangle 20 0, .triangle 10 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0]

-- Cycle fingerprint e8ba35ab1f430aa73eb812c2e9918c827369b0084b1f441ef23bb2dcda4eb5b3.
def localCycle00376 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4]
    constant := ![-1, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 19 0, .triangle 20 2, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint e8d6445f3451cde4d3b012655461076b83b8fc573ae3d92f62cd9d99094c1d0d.
def localCycle00377 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e984789e413552df22791401367d2490383f124f2c6efd1053cc2089cf96e354.
def localCycle00378 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 2, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint ea215407c1010c8ce1bbfc48f35c8c40004eefaade2bc3cc578ba7b3b70bac0a.
def localCycle00379 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint ea742d39e2591d724455e150f90b3e9502587597130b5652e72021728e2369af.
def localCycle00380 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .triangle 3 2, .triangle 12 1, .corridorLower 4 5]

-- Cycle fingerprint eac5669ffd40cc64d19701cd04b72bf74594bcc3d6542594131094a292c93d43.
def localCycle00381 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint ebfd76ae3e3adaa1042c1224826199d9c7587106ee3e9890481b485b314add19.
def localCycle00382 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0]

-- Cycle fingerprint ed30e46151324b77877b19eadd9092925eb02a7bed9f12f4cf261d54aae673ee.
def localCycle00383 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![0, -1, -1, 0, 0, 3, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 17 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint ed8c5cb4d7bc8981e1c7d168896bb60515fa165747f8fec8905bf8d687feacab.
def localCycle00384 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4]
    constant := ![3, -1, 0, -1, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4]

-- Cycle fingerprint ee8b2204afd77912b49cc422559baf882ed9092fa26212e07f1f373768bb2163.
def localCycle00385 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint ef4cfe4a99231008ef49ba7099b0478f8e7685c127b57242abb814053657bbcf.
def localCycle00386 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 18 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint f00b0488e3248fcb914a21bc03ef47793e31fb8ba6e751872d828fdd9f6ceee2.
def localCycle00387 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint f08bf009e0f0901d2d3e3d9162592980665b226d924bea9eb79349c7b8de0f1e.
def localCycle00388 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 0 6]
    constant := ![0, 0, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true] }
  origin := ![.triangle 13 1, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 4, .triangle 4 2]

-- Cycle fingerprint f13de0f3e2ce5517725d21e5d9134dee210fee5fe0d60c0862c77b1a93849194.
def localCycle00389 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, -1, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint f2ef6e694badc7a9dfe1b429a6b451939fd1a4faf9942801912cf1af4ce67d8e.
def localCycle00390 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 33 1, .triangle 20 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3]

-- Cycle fingerprint f415e2377affca08d00a8acf6fd3abed2e428ffa69d8129f1aabd9f73fc7ebf6.
def localCycle00391 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6]
    constant := ![0, -2, -1, -1, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 23 2]

-- Cycle fingerprint f485f63e7494db9808a463c3d9e00dad33855fb5645da5c09703df29ccbec281.
def localCycle00392 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 5]
    constant := ![-1, -2, -2, 0, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 17 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 2]

-- Cycle fingerprint f4aa6c9bf671a1c495c8505cad9536e30ea47b47e142259b72b0c65a698ce8bc.
def localCycle00393 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -2, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint f5c1685e013c9c90ae745a5e0aa05f6a150db0a07a4e5f28ab9ccdc73a134436.
def localCycle00394 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 0, 3, -1, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 30 1, .triangle 17 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint f5d49a280817d08db13e784f24359c90431e6d34c359200854c33e3485bdc64c.
def localCycle00395 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint f5ebd9eb1d535c81b780118bf6b7c38242792b5619b6fb1bfa5ae243e4474fea.
def localCycle00396 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 30 1, .triangle 17 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint f6a53982625753bc7289c1929fbfeb2e863ea2802a7ecc7afe720640891648e7.
def localCycle00397 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 16 0, .gapLower 1 3, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint f6ed8230b39601d3b9cae7c6b0c1a94cb2e0625b9c74bf7e006361f83eab05e1.
def localCycle00398 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1]

-- Cycle fingerprint f7264cb87561645ea2db0eb2cc16a6a5189978f9145e8f38f857b2651af96659.
def localCycle00399 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 1 6]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 18 2]

-- Cycle fingerprint f7da6d28293cc001b2555acb13a055030f7651ac95a2bb5700f4ec96358925ea.
def localCycle00400 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 5]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 17 2]

-- Cycle fingerprint f814cca5bfb3863b01e5ab8df52a47581bafc47986ff25690635bb49c1b01272.
def localCycle00401 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 33 1, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint f822349d8725ac4e86bf50864f7d7379d2ab70c57165ee1b8dcc8fc14700e52c.
def localCycle00402 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, 0, -1, 0, -2, 0, 0, -1, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 3, .gapLower 1 4, .triangle 20 1, .triangle 15 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint f84183ad9de4f4df9de63ba703a80b4baddb01863458b94b810d7889735ce0d0.
def localCycle00403 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 15 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint f8531189eb0c4c77a3dfb7e99d7c730864b17660c02d765effb90e001a1a8a00.
def localCycle00404 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 1, .theta 0]
    constant := ![0, 0, 3, -1, 0, 0, -1, -1, -3, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 30 1, .triangle 17 0, .triangle 0 0, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint f916cc537e4bca96fac2ab6c97a7fad1bdb2d3abeef208ecded2ac621ecb7b35.
def localCycle00405 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint f92027ee0263548588ffcc06f96980aa5edfad677b3666875a16b1ad7fb6e0f5.
def localCycle00406 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint fa562680b29ae375cf4601ea4d55ad10c8f30de874f3a47a23472e15e3a57195.
def localCycle00407 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4]
    constant := ![0, 0, -1, 0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 3, .gapLower 1 4, .triangle 20 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint fa6ff66e780d1dc32f8cff4ab785927ab0256466ba3ae0dd4c00b70e5f1a8982.
def localCycle00408 : Cycle where
  length := 5
  data := {
    node := ![.distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true] }
  origin := ![.triangle 27 2, .gapUpper 2 5, .triangle 15 2, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint fb03f7b3ae97c8495d90157ba8a6ebbaf39dbbb47082cd161d0eb0f49a4807cc.
def localCycle00409 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .gapLower 4 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint fb2642c7fb7ee8ad5c8965c1478fe20e8d31d226bf7d5dc44f240f5f4cd35f64.
def localCycle00410 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint fb43991d3385eaae43f733c86fa35ef10434e070c6aef7b30a37219b26c6dd17.
def localCycle00411 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 0 3, .distance 0 2, .theta 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![-2, 0, -1, 0, -1, 0, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .triangle 18 1, .triangle 17 0, .triangle 26 1, .triangle 10 0, .gapLower 0 2, .gapLower 2 0, .thetaNext 1, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint fd230dfed9510385af7cbea56e1ccff3e49576fbb5fdffd37448285663315c4c.
def localCycle00412 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint fd5bce5cf8136f37000dcb1167c67627faf6c1b64b2a5a7f0e11658360062a86.
def localCycle00413 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint fd75e9beb65379f9c95ad9e885161e9648e67314d7cef679cd62505cd1a1e1a4.
def localCycle00414 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint fd80dc281964c72c058ce0c1b0703ae621a2304cb7d20ddab7838657b65c7746.
def localCycle00415 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -1, -1, 0, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint fe80146ff7ad4f6d1a95ec40925ab0c863d9e540a1ed2e5547e6ce7004769a72.
def localCycle00416 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 5, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 5]
    constant := ![0, -1, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 12 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 1 3, .triangle 3 2]

-- Cycle fingerprint fee0c99acb9445327320db3ffca86a215b0b10dbe36465de709977e31716f70a.
def localCycle00417 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 18 1, .triangle 15 0, .triangle 5 0, .gapLower 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint ff0ac10f60e5fe72938d925ada18dce19870247254fff174500b148e4a855482.
def localCycle00418 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![-1, -1, 0, 0, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.triangle 15 0, .triangle 17 0, .gapLower 2 1, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint fff793fbdca27929fdd8da9cd72ed03cb4f512a39620d71d5be81753872a1969.
def localCycle00419 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

def library : Library := fun id => if id < 210 then (if id < 105 then (if id < 52 then (if id < 26 then (if id < 13 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none))))) else (if id < 19 then (if id < 16 then (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none))) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)))) else (if id < 22 then (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none))) else (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)))))) else (if id < 39 then (if id < 32 then (if id < 29 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none))) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)))) else (if id < 35 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none))) else (if id < 37 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none)) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))))) else (if id < 45 then (if id < 42 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none)))) else (if id < 48 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none))) else (if id < 50 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))))))) else (if id < 78 then (if id < 65 then (if id < 58 then (if id < 55 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none))) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)))) else (if id < 61 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))) else (if id < 63 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none))))) else (if id < 71 then (if id < 68 then (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none))) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)))) else (if id < 74 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none))) else (if id < 76 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)))))) else (if id < 91 then (if id < 84 then (if id < 81 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none))) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)))) else (if id < 87 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none))) else (if id < 89 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none))))) else (if id < 98 then (if id < 94 then (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none))) else (if id < 96 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)))) else (if id < 101 then (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))) else (if id < 103 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)))))))) else (if id < 157 then (if id < 131 then (if id < 118 then (if id < 111 then (if id < 108 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none))) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)))) else (if id < 114 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none))) else (if id < 116 then (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none)) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none))))) else (if id < 124 then (if id < 121 then (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none))) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)))) else (if id < 127 then (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none))) else (if id < 129 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)))))) else (if id < 144 then (if id < 137 then (if id < 134 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none))) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)))) else (if id < 140 then (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none))) else (if id < 142 then (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none)) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none))))) else (if id < 150 then (if id < 147 then (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none))) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none)))) else (if id < 153 then (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none))) else (if id < 155 then (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none)) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none))))))) else (if id < 183 then (if id < 170 then (if id < 163 then (if id < 160 then (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none))) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none)))) else (if id < 166 then (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none))) else (if id < 168 then (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none)) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none))))) else (if id < 176 then (if id < 173 then (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none))) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id = 175 then some localCycle00175 else none)))) else (if id < 179 then (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id = 178 then some localCycle00178 else none))) else (if id < 181 then (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none)) else (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none)))))) else (if id < 196 then (if id < 189 then (if id < 186 then (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id = 185 then some localCycle00185 else none))) else (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none)))) else (if id < 192 then (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id = 191 then some localCycle00191 else none))) else (if id < 194 then (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id = 193 then some localCycle00193 else none)) else (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none))))) else (if id < 203 then (if id < 199 then (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id = 198 then some localCycle00198 else none))) else (if id < 201 then (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id = 200 then some localCycle00200 else none)) else (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none)))) else (if id < 206 then (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none))) else (if id < 208 then (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none)) else (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none))))))))) else (if id < 315 then (if id < 262 then (if id < 236 then (if id < 223 then (if id < 216 then (if id < 213 then (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id = 212 then some localCycle00212 else none))) else (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none)))) else (if id < 219 then (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id = 218 then some localCycle00218 else none))) else (if id < 221 then (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id = 220 then some localCycle00220 else none)) else (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id = 222 then some localCycle00222 else none))))) else (if id < 229 then (if id < 226 then (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id = 225 then some localCycle00225 else none))) else (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id < 228 then (if id = 227 then some localCycle00227 else none) else (if id = 228 then some localCycle00228 else none)))) else (if id < 232 then (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id < 231 then (if id = 230 then some localCycle00230 else none) else (if id = 231 then some localCycle00231 else none))) else (if id < 234 then (if id < 233 then (if id = 232 then some localCycle00232 else none) else (if id = 233 then some localCycle00233 else none)) else (if id < 235 then (if id = 234 then some localCycle00234 else none) else (if id = 235 then some localCycle00235 else none)))))) else (if id < 249 then (if id < 242 then (if id < 239 then (if id < 237 then (if id = 236 then some localCycle00236 else none) else (if id < 238 then (if id = 237 then some localCycle00237 else none) else (if id = 238 then some localCycle00238 else none))) else (if id < 240 then (if id = 239 then some localCycle00239 else none) else (if id < 241 then (if id = 240 then some localCycle00240 else none) else (if id = 241 then some localCycle00241 else none)))) else (if id < 245 then (if id < 243 then (if id = 242 then some localCycle00242 else none) else (if id < 244 then (if id = 243 then some localCycle00243 else none) else (if id = 244 then some localCycle00244 else none))) else (if id < 247 then (if id < 246 then (if id = 245 then some localCycle00245 else none) else (if id = 246 then some localCycle00246 else none)) else (if id < 248 then (if id = 247 then some localCycle00247 else none) else (if id = 248 then some localCycle00248 else none))))) else (if id < 255 then (if id < 252 then (if id < 250 then (if id = 249 then some localCycle00249 else none) else (if id < 251 then (if id = 250 then some localCycle00250 else none) else (if id = 251 then some localCycle00251 else none))) else (if id < 253 then (if id = 252 then some localCycle00252 else none) else (if id < 254 then (if id = 253 then some localCycle00253 else none) else (if id = 254 then some localCycle00254 else none)))) else (if id < 258 then (if id < 256 then (if id = 255 then some localCycle00255 else none) else (if id < 257 then (if id = 256 then some localCycle00256 else none) else (if id = 257 then some localCycle00257 else none))) else (if id < 260 then (if id < 259 then (if id = 258 then some localCycle00258 else none) else (if id = 259 then some localCycle00259 else none)) else (if id < 261 then (if id = 260 then some localCycle00260 else none) else (if id = 261 then some localCycle00261 else none))))))) else (if id < 288 then (if id < 275 then (if id < 268 then (if id < 265 then (if id < 263 then (if id = 262 then some localCycle00262 else none) else (if id < 264 then (if id = 263 then some localCycle00263 else none) else (if id = 264 then some localCycle00264 else none))) else (if id < 266 then (if id = 265 then some localCycle00265 else none) else (if id < 267 then (if id = 266 then some localCycle00266 else none) else (if id = 267 then some localCycle00267 else none)))) else (if id < 271 then (if id < 269 then (if id = 268 then some localCycle00268 else none) else (if id < 270 then (if id = 269 then some localCycle00269 else none) else (if id = 270 then some localCycle00270 else none))) else (if id < 273 then (if id < 272 then (if id = 271 then some localCycle00271 else none) else (if id = 272 then some localCycle00272 else none)) else (if id < 274 then (if id = 273 then some localCycle00273 else none) else (if id = 274 then some localCycle00274 else none))))) else (if id < 281 then (if id < 278 then (if id < 276 then (if id = 275 then some localCycle00275 else none) else (if id < 277 then (if id = 276 then some localCycle00276 else none) else (if id = 277 then some localCycle00277 else none))) else (if id < 279 then (if id = 278 then some localCycle00278 else none) else (if id < 280 then (if id = 279 then some localCycle00279 else none) else (if id = 280 then some localCycle00280 else none)))) else (if id < 284 then (if id < 282 then (if id = 281 then some localCycle00281 else none) else (if id < 283 then (if id = 282 then some localCycle00282 else none) else (if id = 283 then some localCycle00283 else none))) else (if id < 286 then (if id < 285 then (if id = 284 then some localCycle00284 else none) else (if id = 285 then some localCycle00285 else none)) else (if id < 287 then (if id = 286 then some localCycle00286 else none) else (if id = 287 then some localCycle00287 else none)))))) else (if id < 301 then (if id < 294 then (if id < 291 then (if id < 289 then (if id = 288 then some localCycle00288 else none) else (if id < 290 then (if id = 289 then some localCycle00289 else none) else (if id = 290 then some localCycle00290 else none))) else (if id < 292 then (if id = 291 then some localCycle00291 else none) else (if id < 293 then (if id = 292 then some localCycle00292 else none) else (if id = 293 then some localCycle00293 else none)))) else (if id < 297 then (if id < 295 then (if id = 294 then some localCycle00294 else none) else (if id < 296 then (if id = 295 then some localCycle00295 else none) else (if id = 296 then some localCycle00296 else none))) else (if id < 299 then (if id < 298 then (if id = 297 then some localCycle00297 else none) else (if id = 298 then some localCycle00298 else none)) else (if id < 300 then (if id = 299 then some localCycle00299 else none) else (if id = 300 then some localCycle00300 else none))))) else (if id < 308 then (if id < 304 then (if id < 302 then (if id = 301 then some localCycle00301 else none) else (if id < 303 then (if id = 302 then some localCycle00302 else none) else (if id = 303 then some localCycle00303 else none))) else (if id < 306 then (if id < 305 then (if id = 304 then some localCycle00304 else none) else (if id = 305 then some localCycle00305 else none)) else (if id < 307 then (if id = 306 then some localCycle00306 else none) else (if id = 307 then some localCycle00307 else none)))) else (if id < 311 then (if id < 309 then (if id = 308 then some localCycle00308 else none) else (if id < 310 then (if id = 309 then some localCycle00309 else none) else (if id = 310 then some localCycle00310 else none))) else (if id < 313 then (if id < 312 then (if id = 311 then some localCycle00311 else none) else (if id = 312 then some localCycle00312 else none)) else (if id < 314 then (if id = 313 then some localCycle00313 else none) else (if id = 314 then some localCycle00314 else none)))))))) else (if id < 367 then (if id < 341 then (if id < 328 then (if id < 321 then (if id < 318 then (if id < 316 then (if id = 315 then some localCycle00315 else none) else (if id < 317 then (if id = 316 then some localCycle00316 else none) else (if id = 317 then some localCycle00317 else none))) else (if id < 319 then (if id = 318 then some localCycle00318 else none) else (if id < 320 then (if id = 319 then some localCycle00319 else none) else (if id = 320 then some localCycle00320 else none)))) else (if id < 324 then (if id < 322 then (if id = 321 then some localCycle00321 else none) else (if id < 323 then (if id = 322 then some localCycle00322 else none) else (if id = 323 then some localCycle00323 else none))) else (if id < 326 then (if id < 325 then (if id = 324 then some localCycle00324 else none) else (if id = 325 then some localCycle00325 else none)) else (if id < 327 then (if id = 326 then some localCycle00326 else none) else (if id = 327 then some localCycle00327 else none))))) else (if id < 334 then (if id < 331 then (if id < 329 then (if id = 328 then some localCycle00328 else none) else (if id < 330 then (if id = 329 then some localCycle00329 else none) else (if id = 330 then some localCycle00330 else none))) else (if id < 332 then (if id = 331 then some localCycle00331 else none) else (if id < 333 then (if id = 332 then some localCycle00332 else none) else (if id = 333 then some localCycle00333 else none)))) else (if id < 337 then (if id < 335 then (if id = 334 then some localCycle00334 else none) else (if id < 336 then (if id = 335 then some localCycle00335 else none) else (if id = 336 then some localCycle00336 else none))) else (if id < 339 then (if id < 338 then (if id = 337 then some localCycle00337 else none) else (if id = 338 then some localCycle00338 else none)) else (if id < 340 then (if id = 339 then some localCycle00339 else none) else (if id = 340 then some localCycle00340 else none)))))) else (if id < 354 then (if id < 347 then (if id < 344 then (if id < 342 then (if id = 341 then some localCycle00341 else none) else (if id < 343 then (if id = 342 then some localCycle00342 else none) else (if id = 343 then some localCycle00343 else none))) else (if id < 345 then (if id = 344 then some localCycle00344 else none) else (if id < 346 then (if id = 345 then some localCycle00345 else none) else (if id = 346 then some localCycle00346 else none)))) else (if id < 350 then (if id < 348 then (if id = 347 then some localCycle00347 else none) else (if id < 349 then (if id = 348 then some localCycle00348 else none) else (if id = 349 then some localCycle00349 else none))) else (if id < 352 then (if id < 351 then (if id = 350 then some localCycle00350 else none) else (if id = 351 then some localCycle00351 else none)) else (if id < 353 then (if id = 352 then some localCycle00352 else none) else (if id = 353 then some localCycle00353 else none))))) else (if id < 360 then (if id < 357 then (if id < 355 then (if id = 354 then some localCycle00354 else none) else (if id < 356 then (if id = 355 then some localCycle00355 else none) else (if id = 356 then some localCycle00356 else none))) else (if id < 358 then (if id = 357 then some localCycle00357 else none) else (if id < 359 then (if id = 358 then some localCycle00358 else none) else (if id = 359 then some localCycle00359 else none)))) else (if id < 363 then (if id < 361 then (if id = 360 then some localCycle00360 else none) else (if id < 362 then (if id = 361 then some localCycle00361 else none) else (if id = 362 then some localCycle00362 else none))) else (if id < 365 then (if id < 364 then (if id = 363 then some localCycle00363 else none) else (if id = 364 then some localCycle00364 else none)) else (if id < 366 then (if id = 365 then some localCycle00365 else none) else (if id = 366 then some localCycle00366 else none))))))) else (if id < 393 then (if id < 380 then (if id < 373 then (if id < 370 then (if id < 368 then (if id = 367 then some localCycle00367 else none) else (if id < 369 then (if id = 368 then some localCycle00368 else none) else (if id = 369 then some localCycle00369 else none))) else (if id < 371 then (if id = 370 then some localCycle00370 else none) else (if id < 372 then (if id = 371 then some localCycle00371 else none) else (if id = 372 then some localCycle00372 else none)))) else (if id < 376 then (if id < 374 then (if id = 373 then some localCycle00373 else none) else (if id < 375 then (if id = 374 then some localCycle00374 else none) else (if id = 375 then some localCycle00375 else none))) else (if id < 378 then (if id < 377 then (if id = 376 then some localCycle00376 else none) else (if id = 377 then some localCycle00377 else none)) else (if id < 379 then (if id = 378 then some localCycle00378 else none) else (if id = 379 then some localCycle00379 else none))))) else (if id < 386 then (if id < 383 then (if id < 381 then (if id = 380 then some localCycle00380 else none) else (if id < 382 then (if id = 381 then some localCycle00381 else none) else (if id = 382 then some localCycle00382 else none))) else (if id < 384 then (if id = 383 then some localCycle00383 else none) else (if id < 385 then (if id = 384 then some localCycle00384 else none) else (if id = 385 then some localCycle00385 else none)))) else (if id < 389 then (if id < 387 then (if id = 386 then some localCycle00386 else none) else (if id < 388 then (if id = 387 then some localCycle00387 else none) else (if id = 388 then some localCycle00388 else none))) else (if id < 391 then (if id < 390 then (if id = 389 then some localCycle00389 else none) else (if id = 390 then some localCycle00390 else none)) else (if id < 392 then (if id = 391 then some localCycle00391 else none) else (if id = 392 then some localCycle00392 else none)))))) else (if id < 406 then (if id < 399 then (if id < 396 then (if id < 394 then (if id = 393 then some localCycle00393 else none) else (if id < 395 then (if id = 394 then some localCycle00394 else none) else (if id = 395 then some localCycle00395 else none))) else (if id < 397 then (if id = 396 then some localCycle00396 else none) else (if id < 398 then (if id = 397 then some localCycle00397 else none) else (if id = 398 then some localCycle00398 else none)))) else (if id < 402 then (if id < 400 then (if id = 399 then some localCycle00399 else none) else (if id < 401 then (if id = 400 then some localCycle00400 else none) else (if id = 401 then some localCycle00401 else none))) else (if id < 404 then (if id < 403 then (if id = 402 then some localCycle00402 else none) else (if id = 403 then some localCycle00403 else none)) else (if id < 405 then (if id = 404 then some localCycle00404 else none) else (if id = 405 then some localCycle00405 else none))))) else (if id < 413 then (if id < 409 then (if id < 407 then (if id = 406 then some localCycle00406 else none) else (if id < 408 then (if id = 407 then some localCycle00407 else none) else (if id = 408 then some localCycle00408 else none))) else (if id < 411 then (if id < 410 then (if id = 409 then some localCycle00409 else none) else (if id = 410 then some localCycle00410 else none)) else (if id < 412 then (if id = 411 then some localCycle00411 else none) else (if id = 412 then some localCycle00412 else none)))) else (if id < 416 then (if id < 414 then (if id = 413 then some localCycle00413 else none) else (if id < 415 then (if id = 414 then some localCycle00414 else none) else (if id = 415 then some localCycle00415 else none))) else (if id < 418 then (if id < 417 then (if id = 416 then some localCycle00416 else none) else (if id = 417 then some localCycle00417 else none)) else (if id < 419 then (if id = 418 then some localCycle00418 else none) else (if id = 419 then some localCycle00419 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 4, 3, 6, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 4, 1, 6], ![5, 0, 2, 3, 1, 6], ![4, 0, 2, 3, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 387 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1536)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 4, 6, 3, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 4, 6, 1], ![5, 0, 2, 3, 1, 6], ![4, 0, 2, 3, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .low (![226, 405, 64, 176, 181, 136, 130, 75, 106, 32, 408, 126, 162, 106, 335, 408, 126, 287, 332, 106, 126, 106, 63, 126, 142, 126, 23, 297]) }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1537)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 4, 6, 1], ![5, 0, 2, 3, 6, 1], ![4, 0, 2, 3, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 161 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1538)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 6, 4, 1], ![5, 0, 2, 6, 3, 1], ![4, 0, 2, 3, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 81 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1539)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 5, 6, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 2, 3, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 413 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1540)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 4, 6, 1], ![5, 0, 2, 3, 6, 1], ![4, 0, 2, 3, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 318 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1541)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 6, 4, 1], ![5, 0, 2, 6, 3, 1], ![4, 0, 2, 3, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 81 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1542)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 6, 5, 4, 1], ![5, 0, 2, 6, 3, 1], ![4, 0, 2, 6, 3, 1], ![0, 2, 4, 5, 3, 1]], proof := .tail 94 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1543)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 5, 6, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 2, 3, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 413 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1544)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 6, 5, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 2, 6, 3, 1], ![0, 4, 2, 5, 3, 1]], proof := .tail 94 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1545)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 5, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 6, 2, 3, 1], ![0, 4, 5, 2, 3, 1]], proof := .tail 147 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1546)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 5, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 6, 2, 3, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 31 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1547)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 4, 3, 2, 6], ![0, 5, 3, 4, 1, 6], ![0, 5, 2, 4, 1, 6], ![5, 0, 2, 3, 1, 6], ![4, 0, 3, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 193 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1548)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 4, 3, 6, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 4, 1, 6], ![5, 0, 2, 3, 1, 6], ![4, 0, 3, 2, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 193 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1549)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 4, 6, 1], ![5, 0, 2, 3, 1, 6], ![4, 0, 3, 2, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 273 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1550)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 4, 6, 1], ![5, 0, 2, 3, 6, 1], ![4, 0, 3, 2, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 179 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1551)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 6, 4, 1], ![5, 0, 2, 6, 3, 1], ![4, 0, 3, 2, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 11 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1552)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 3, 6, 4, 1], ![0, 5, 2, 6, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 3, 2, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 413 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1553)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 3, 4, 1], ![0, 5, 6, 2, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 13 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1554)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 4, 6, 1], ![5, 0, 2, 3, 6, 1], ![4, 0, 3, 2, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 149 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1555)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 6, 4, 1], ![5, 0, 2, 6, 3, 1], ![4, 0, 3, 2, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 11 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1556)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 3, 6, 4, 1], ![0, 5, 2, 6, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 3, 2, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 413 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1557)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 3, 4, 1], ![0, 5, 6, 2, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 3, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 13 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1558)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 3, 4, 1], ![0, 5, 6, 2, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 3, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 37 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1559)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 3, 4, 1], ![0, 6, 5, 2, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 6, 3, 2, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 227 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1560)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 1, 6], ![0, 5, 4, 2, 1, 6], ![5, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 102 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1561)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 4, 3, 6, 2], ![0, 5, 4, 3, 6, 1], ![0, 5, 4, 2, 1, 6], ![5, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 216 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1562)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 3, 6, 1], ![0, 5, 4, 2, 6, 1], ![5, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 276 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1563)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 1], ![0, 5, 4, 6, 2, 1], ![5, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 233 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1564)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 3, 6, 1], ![0, 5, 4, 2, 6, 1], ![5, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 77 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1565)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![0, 5, 4, 6, 2, 1], ![5, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 110 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1566)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![0, 5, 4, 6, 2, 1], ![5, 0, 3, 6, 2, 1], ![4, 0, 3, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 328 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1567)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![0, 5, 6, 4, 2, 1], ![5, 0, 6, 3, 2, 1], ![4, 0, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 39 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1568)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 3, 6, 1], ![0, 5, 4, 2, 6, 1], ![5, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 367 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1569)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![0, 5, 4, 6, 2, 1], ![5, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 125 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1570)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![0, 5, 4, 6, 2, 1], ![5, 0, 3, 6, 2, 1], ![4, 0, 3, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 328 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1571)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![0, 5, 6, 4, 2, 1], ![5, 0, 6, 3, 2, 1], ![4, 0, 3, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 39 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1572)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![0, 5, 4, 6, 2, 1], ![5, 0, 3, 6, 2, 1], ![4, 0, 3, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 409 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1573)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![0, 5, 6, 4, 2, 1], ![5, 0, 6, 3, 2, 1], ![4, 0, 3, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 201 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1574)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![0, 6, 5, 4, 2, 1], ![5, 0, 6, 3, 2, 1], ![4, 0, 6, 3, 2, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 36 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1575)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 5, 6, 4], ![0, 1, 3, 5, 6, 4], ![0, 1, 2, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 2, 3, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 80 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1576)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 5, 6, 4], ![0, 1, 3, 5, 6, 4], ![0, 1, 2, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 2, 6, 3], ![4, 0, 1, 2, 5, 3]], proof := .tail 146 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1577)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 5, 6, 4], ![0, 1, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 6, 2, 3], ![4, 0, 1, 5, 2, 3]], proof := .low (![361, 299, 178, 135, 79, 217, 238, 65, 393, 275, 402, 364, 104, 29, 403, 122, 386, 365, 247, 407, 236, 415, 151, 292, 292, 58, 160, 5]) }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1578)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 5, 6, 4], ![0, 1, 6, 3, 5, 4], ![0, 1, 6, 2, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 6, 2, 3], ![4, 0, 1, 5, 3, 2]], proof := .tail 120 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1579)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 5, 6, 4], ![0, 1, 5, 3, 6, 4], ![0, 1, 5, 2, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 3, 2, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 324 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1580)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 5, 6, 4], ![0, 1, 5, 6, 3, 4], ![0, 1, 5, 6, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 3, 2, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 271 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1581)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 5, 6, 4], ![0, 1, 6, 5, 3, 4], ![0, 1, 5, 6, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 3, 6, 2], ![4, 0, 1, 3, 5, 2]], proof := .tail 55 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1582)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 5, 6, 4], ![0, 1, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 6, 3, 2], ![4, 0, 1, 5, 3, 2]], proof := .tail 89 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1583)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 6, 5, 4], ![0, 1, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![4, 0, 5, 1, 2, 3]], proof := .low (![352, 299, 178, 87, 283, 228, 192, 65, 395, 145, 331, 281, 168, 29, 211, 309, 281, 365, 10, 185, 281, 343, 357, 281, 35, 294, 66, 304]) }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1584)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 3, 5, 4], ![0, 1, 6, 2, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![4, 0, 5, 1, 3, 2]], proof := .tail 120 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1585)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 3, 2], ![4, 0, 5, 1, 3, 2]], proof := .tail 89 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1586)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![4, 0, 5, 3, 1, 2]], proof := .tail 260 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1587)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 3, 2], ![4, 0, 5, 3, 1, 2]], proof := .tail 141 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1588)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 5, 3, 6, 4], ![0, 1, 5, 3, 6, 4], ![0, 5, 1, 2, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 1, 2, 6], ![4, 0, 1, 2, 3, 5]], proof := .low (![288, 384, 165, 204, 144, 112, 0, 392, 166, 101, 306, 40, 375, 116, 279, 74, 386, 172, 284, 2, 109, 376, 208, 374, 380, 51, 95, 143]) }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1589)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 5, 3, 6, 4], ![0, 1, 5, 6, 3, 4], ![0, 5, 1, 6, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 1, 2, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 339 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1590)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 5, 3, 6, 4], ![0, 1, 6, 5, 3, 4], ![0, 5, 1, 6, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 1, 6, 2], ![4, 0, 1, 3, 5, 2]], proof := .tail 54 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1591)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 5, 6, 3, 4], ![0, 1, 5, 6, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 1, 2, 6], ![4, 0, 3, 1, 2, 5]], proof := .low (![404, 199, 165, 197, 225, 173, 154, 394, 212, 316, 14, 363, 237, 67, 127, 191, 203, 396, 84, 18, 358, 344, 398, 50, 416, 188, 388, 190]) }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1592)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 5, 6, 3, 4], ![0, 1, 6, 5, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 1, 6, 2], ![4, 0, 3, 1, 5, 2]], proof := .tail 52 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1593)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 6, 1, 2], ![4, 0, 3, 5, 1, 2]], proof := .tail 73 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1594)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 3, 1, 2], ![4, 0, 5, 3, 1, 2]], proof := .tail 83 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1595)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![4, 0, 5, 3, 2, 1]], proof := .tail 308 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1596)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 3, 2], ![4, 0, 5, 3, 2, 1]], proof := .tail 141 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1597)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 6, 1, 2], ![4, 0, 3, 5, 2, 1]], proof := .tail 381 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1598)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 3, 1, 2], ![4, 0, 5, 3, 2, 1]], proof := .tail 83 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1599)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 2, 3, 6, 4], ![0, 5, 1, 3, 6, 4], ![0, 5, 1, 2, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 2, 1, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 9 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1600)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 2, 3, 6, 4], ![0, 5, 1, 6, 3, 4], ![0, 5, 1, 6, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 2, 1, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 140 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1601)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 2, 6, 3, 4], ![0, 5, 1, 6, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 2, 1, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 16 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1602)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 2, 3, 4], ![0, 5, 6, 1, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 5]], proof := .tail 99 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1603)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 2, 3, 4], ![0, 5, 6, 1, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 5, 1]], proof := .tail 239 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1604)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 6, 2, 1], ![4, 0, 3, 5, 2, 1]], proof := .tail 305 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1605)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 3, 4], ![0, 6, 5, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 3, 2, 1], ![4, 0, 5, 3, 2, 1]], proof := .tail 88 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1606)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 2, 5, 6, 4], ![0, 3, 1, 5, 6, 4], ![0, 2, 1, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 2, 3, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 293 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1607)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 2, 5, 6, 4], ![0, 3, 1, 5, 6, 4], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 2, 6, 3], ![4, 0, 1, 2, 5, 3]], proof := .tail 406 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1608)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 2, 5, 6, 4], ![0, 3, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 6, 2, 3], ![4, 0, 1, 5, 2, 3]], proof := .tail 138 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1609)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 2, 6, 5, 4], ![0, 3, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![4, 0, 5, 1, 2, 3]], proof := .low (![224, 312, 231, 254, 283, 228, 192, 366, 164, 105, 417, 281, 168, 184, 105, 353, 281, 187, 7, 184, 281, 184, 263, 281, 346, 294, 255, 304]) }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1610)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 6, 2, 5, 4], ![0, 3, 6, 1, 5, 4], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![4, 0, 5, 2, 1, 3]], proof := .tail 49 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1611)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 3, 2, 5, 4], ![0, 3, 6, 1, 5, 4], ![0, 2, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![4, 0, 5, 2, 3, 1]], proof := .tail 85 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1612)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 3, 2, 5, 4], ![0, 6, 3, 1, 5, 4], ![0, 6, 2, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![4, 0, 5, 3, 2, 1]], proof := .tail 337 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1613)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 5, 2, 6, 4], ![0, 3, 5, 1, 6, 4], ![0, 2, 1, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 1, 3, 6], ![4, 0, 1, 2, 3, 5]], proof := .low (![310, 382, 251, 307, 258, 139, 313, 286, 350, 272, 129, 213, 104, 78, 359, 148, 303, 351, 397, 182, 214, 56, 289, 296, 243, 265, 322, 334]) }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1614)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 5, 2, 6, 4], ![0, 3, 5, 1, 6, 4], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 1, 6, 3], ![4, 0, 1, 2, 5, 3]], proof := .tail 3 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1615)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 3, 2, 6, 4], ![0, 3, 5, 1, 6, 4], ![0, 2, 5, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 3, 1, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 333 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1616)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 3, 2, 6, 4], ![0, 5, 3, 1, 6, 4], ![0, 5, 2, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 2, 1, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 59 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1617)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 5, 6, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 1, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 1, 3, 6], ![4, 0, 2, 1, 3, 5]], proof := .low (![33, 382, 251, 43, 152, 267, 24, 286, 295, 240, 235, 57, 104, 158, 170, 278, 336, 351, 264, 270, 355, 82, 302, 159, 8, 372, 115, 356]) }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1618)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 5, 6, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 1, 6, 3], ![4, 0, 2, 1, 5, 3]], proof := .low (![33, 274, 90, 347, 152, 267, 24, 370, 362, 240, 235, 57, 104, 326, 170, 278, 336, 86, 264, 270, 169, 169, 302, 159, 8, 372, 115, 356]) }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1619)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 6, 5, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 6, 1, 3], ![4, 0, 2, 5, 1, 3]], proof := .tail 319 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1620)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 6, 5, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 2, 1, 3], ![4, 0, 5, 2, 1, 3]], proof := .tail 317 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1621)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 3, 5, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 6, 1, 3], ![4, 0, 2, 5, 3, 1]], proof := .tail 28 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1622)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 3, 5, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 2, 1, 3], ![4, 0, 5, 2, 3, 1]], proof := .tail 317 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1623)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 3, 5, 2, 4], ![0, 6, 3, 5, 1, 4], ![0, 6, 2, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 2, 1, 3], ![4, 0, 5, 3, 2, 1]], proof := .tail 206 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1624)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 3, 6, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 5, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 3, 1, 6], ![4, 0, 2, 1, 3, 5]], proof := .tail 290 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1625)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 3, 6, 2, 4], ![0, 5, 3, 6, 1, 4], ![0, 5, 2, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 2, 1, 6], ![4, 0, 2, 1, 3, 5]], proof := .tail 117 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1626)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 3, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 5, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 3, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 123 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1627)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 3, 2, 4], ![0, 5, 3, 6, 1, 4], ![0, 5, 2, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 2, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 221 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1628)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 3, 2, 4], ![0, 5, 6, 3, 1, 4], ![0, 5, 6, 2, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 5]], proof := .tail 401 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1629)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 5, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 3, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 414 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1630)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 6, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 6, 3, 1], ![4, 0, 2, 5, 3, 1]], proof := .tail 83 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1631)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 6, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 2, 3, 1], ![4, 0, 5, 2, 3, 1]], proof := .tail 412 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1632)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 2, 4], ![0, 6, 3, 5, 1, 4], ![0, 6, 2, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 2, 3, 1], ![4, 0, 5, 3, 2, 1]], proof := .tail 261 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1633)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 2, 4], ![0, 5, 3, 6, 1, 4], ![0, 5, 2, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 2, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 379 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1634)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 2, 4], ![0, 5, 6, 3, 1, 4], ![0, 5, 6, 2, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 5, 1]], proof := .tail 186 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1635)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 1, 4], ![0, 5, 6, 2, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 6, 2, 1], ![4, 0, 3, 5, 2, 1]], proof := .tail 317 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1636)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 1, 4], ![0, 6, 5, 2, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 3, 2, 1], ![4, 0, 5, 3, 2, 1]], proof := .tail 15 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1637)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 5, 6, 4], ![0, 1, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 1, 3, 2, 6], ![4, 0, 1, 3, 2, 5]], proof := .low (![132, 300, 210, 20, 41, 150, 238, 390, 133, 200, 314, 277, 104, 189, 177, 70, 103, 92, 21, 167, 229, 315, 202, 244, 342, 280, 72, 373]) }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1638)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 5, 3, 6, 4], ![0, 1, 5, 6, 4, 3], ![0, 5, 1, 6, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 1, 2, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 1 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1639)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 5, 6, 3, 4], ![0, 1, 5, 6, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 1, 2, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 377 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1640)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 5, 6, 4], ![0, 1, 6, 5, 4, 3], ![0, 1, 5, 6, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 1, 3, 6, 2], ![4, 0, 1, 3, 5, 2]], proof := .tail 97 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1641)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 5, 6, 4], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 1, 6, 3, 2], ![4, 0, 1, 5, 3, 2]], proof := .tail 93 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1642)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 6, 1, 3, 2], ![4, 0, 5, 1, 3, 2]], proof := .tail 93 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1643)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 6, 1, 3, 2], ![4, 0, 5, 3, 1, 2]], proof := .tail 183 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1644)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 5, 3, 6, 4], ![0, 1, 6, 5, 4, 3], ![0, 5, 1, 6, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 1, 6, 2], ![4, 0, 1, 3, 5, 2]], proof := .tail 195 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1645)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 5, 6, 3, 4], ![0, 1, 6, 5, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 1, 6, 2], ![4, 0, 3, 1, 5, 2]], proof := .tail 377 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1646)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 6, 1, 2], ![4, 0, 3, 5, 1, 2]], proof := .tail 218 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1647)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 6, 3, 1, 2], ![4, 0, 5, 3, 1, 2]], proof := .tail 48 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1648)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 6, 1, 3, 2], ![4, 0, 5, 3, 2, 1]], proof := .tail 183 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1649)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 6, 1, 2], ![4, 0, 3, 5, 2, 1]], proof := .tail 218 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1650)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 6, 3, 1, 2], ![4, 0, 5, 3, 2, 1]], proof := .tail 48 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1651)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 2, 3, 6, 4], ![0, 5, 1, 6, 4, 3], ![0, 5, 1, 6, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 2, 1, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 38 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1652)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 2, 6, 3, 4], ![0, 5, 1, 6, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 2, 1, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 377 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1653)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 2, 3, 4], ![0, 5, 6, 1, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 5]], proof := .tail 196 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1654)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 2, 3, 4], ![0, 5, 6, 1, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 5, 1]], proof := .tail 218 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1655)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 6, 2, 1], ![4, 0, 3, 5, 2, 1]], proof := .tail 250 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1656)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 4, 3], ![0, 6, 5, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 6, 3, 2, 1], ![4, 0, 5, 3, 2, 1]], proof := .tail 48 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1657)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 3, 1, 2, 6], ![4, 0, 3, 1, 2, 5]], proof := .low (![249, 131, 165, 69, 256, 325, 360, 301, 320, 345, 108, 47, 163, 119, 232, 219, 329, 222, 215, 327, 391, 291, 383, 246, 156, 245, 205, 17]) }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1658)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 3, 1, 6, 2], ![4, 0, 3, 1, 5, 2]], proof := .low (![268, 252, 42, 71, 256, 325, 360, 4, 389, 321, 108, 47, 163, 96, 44, 219, 329, 134, 25, 257, 257, 257, 60, 246, 157, 245, 205, 17]) }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1659)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 3, 6, 1, 2], ![4, 0, 3, 5, 1, 2]], proof := .low (![91, 230, 137, 61, 107, 325, 30, 46, 118, 349, 100, 113, 269, 259, 76, 369, 114, 171, 410, 369, 114, 234, 198, 262, 26, 124, 253, 248]) }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1660)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 3, 6, 1, 2], ![4, 0, 3, 5, 2, 1]], proof := .tail 385 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1661)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 3, 2, 1, 6], ![4, 0, 3, 1, 2, 5]], proof := .low (![418, 98, 242, 400, 354, 325, 360, 6, 180, 68, 27, 62, 22, 338, 341, 311, 111, 282, 371, 338, 338, 338, 53, 266, 175, 207, 411, 340]) }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1662)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 5]], proof := .low (![220, 34, 153, 368, 121, 325, 360, 209, 19, 285, 419, 62, 22, 12, 323, 155, 330, 282, 45, 399, 174, 223, 378, 128, 298, 194, 348, 241]) }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1663)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (1536 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 1536 ≤ id.val) (hhigh : id.val < 1664) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 1536)) = true := by
  let j : Fin 128 := ⟨id.val - 1536, by omega⟩
  have hsum : 1536 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (1536 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard012
