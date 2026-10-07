import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard036
open N4R2OuterLeftReplay

-- Cycle fingerprint 056d22a9891d7eb5a14624560d3d7551d37ba67b73bc048901769a754e6778bf.
def localCycle00000 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 1 5]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 20 2]

-- Cycle fingerprint 06781aae7e358d1261eff96a98dbdb215ce5c5e23c2805daed5dd5af072436f8.
def localCycle00001 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2]
    constant := ![-2, -2, 2, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .gapUpper 3 3, .gapUpper 5 5, .gapLower 6 5, .triangle 29 0, .triangle 16 0]

-- Cycle fingerprint 078dcde196a756dbfb8d8db060fcde526cf6193a9d597c00df604996f7f86619.
def localCycle00002 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 2, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .gapLower 1 4, .triangle 17 2]

-- Cycle fingerprint 08e0302c87d76f977fc45aba901641bd6a40867a44e8bbfd9d3a5fe842c120a5.
def localCycle00003 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![-1, -1, 0, 0, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.triangle 19 0, .triangle 20 0, .gapLower 3 2, .triangle 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 09134df7dfcc13caa7dccddac9e6c0700a0f7f71c0ecf64a32f911d7f27284d0.
def localCycle00004 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 2 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![0, 0, -2, 0, 0, 0, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, true, true, true, false, false, false, false, false, true, true] }
  origin := ![.triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 16 1, .triangle 17 2, .triangle 20 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint 09a0004431783e8d3d743c9a3bf7b0e7b6e984a7206d6d918f86fe3ef2cbb4d2.
def localCycle00005 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-1, -1, -1, 0, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 1, .triangle 18 2, .triangle 21 1]

-- Cycle fingerprint 0c4d4dbceb18b86282be8a7a380cb3e3c168c50751c02c32dcc76598e983c268.
def localCycle00006 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 2, .distance 1 6]
    constant := ![0, -1, 0, 0, -1, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, false, true, true, false, true] }
  origin := ![.triangle 21 1, .triangle 20 0, .triangle 26 2, .triangle 28 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 18 2]

-- Cycle fingerprint 0c930c1b689db2febd53b6e4db159c9901de6eb1d34d0414c612f569f3d87890.
def localCycle00007 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, 0, -2, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 6, .triangle 16 1, .gapLower 1 3, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 0d052f08688bbbf4f26086a36844b564a5ce7e09a64715a13aa8a56034f5139d.
def localCycle00008 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 8 0, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 0d62e00e82d4395e2793832af6969205ab2c47ed23cdda37075f8cca412ed6c0.
def localCycle00009 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -1, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 17 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 0e2ba3c658f6fcb5fda9cbd5bb6d9c52bc69388fe1b5293964f71c695fe8fe30.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 3, .distance 3 4, .distance 2 4]
    constant := ![0, -2, 0, -2, -1, -1, 0, 4, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 18 1, .gapLower 1 3, .triangle 20 0, .triangle 26 0, .gapLower 3 0, .gapLower 3 6, .triangle 25 2]

-- Cycle fingerprint 0f543d03da9c97f99b04c53b917d45ef8a57ab9163ec2175f7751d503b7656a5.
def localCycle00011 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 6, .distance 0 3, .distance 3 5, .distance 2 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 0 6]
    constant := ![0, -1, 0, 0, -1, 3, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, false, true, true, false, true] }
  origin := ![.triangle 11 1, .triangle 10 0, .triangle 26 2, .triangle 28 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 4 2]

-- Cycle fingerprint 10ff5ece2121bbc59fb6b66feb8ecdcfcf0ec3afd4803c0c0374ef9a8c1f40ab.
def localCycle00012 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 118a38a46f3532f899870d16ec2889ed20a4dc301926e76e902be5e7a5d02b45.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 20 1, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 13770f29933a48fbd1c7addcd72f0e14dde5be156533f6dcaee681d19ace4399.
def localCycle00014 : Cycle where
  length := 7
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .distance 2 4]
    constant := ![-1, -2, 0, -1, -1, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.triangle 16 0, .gapLower 1 4, .triangle 21 1, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .gapLower 2 6]

-- Cycle fingerprint 146e83e14e51ecf1d95d4638f7202bdf8e8d6cc16e76928359a2d522450967b4.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 5, .distance 3 5, .distance 2 5, .distance 4 5, .theta 4, .distance 3 4]
    constant := ![-1, -2, -2, 0, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, true, false, false] }
  origin := ![.triangle 19 0, .gapLower 1 3, .gapLower 1 2, .triangle 3 2, .triangle 10 1, .triangle 26 2, .triangle 28 1, .corridorLower 4 5, .corridorUpper 3 4]

-- Cycle fingerprint 151cbad0572062fae42a66921e86daef55faa9ae7107a3e07f379a559892b5ac.
def localCycle00016 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 16e7206556359c1cb7a3419a4b3fd4695c82f49f8c35c988fc071762496aff3a.
def localCycle00017 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .gapLower 1 4, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 172185adf0c6553967fdc24b46ac8f764f102c1f9a7098cef611226d37bc411c.
def localCycle00018 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 29 1, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 1a19e56a6f4c801fc8bf54679f782b0930bfd051b4c8985481a89d9f682bf39b.
def localCycle00019 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 2, .gapLower 1 3, .triangle 24 1]

-- Cycle fingerprint 1c40533a8860812e1ab64c3efa969998a8228d4df50257cf3cf39ff5ec6a3319.
def localCycle00020 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 3 5, .gapLower 4 5, .triangle 16 2, .gapLower 1 5, .triangle 15 2]

-- Cycle fingerprint 1e8acb75cc3fc1b968ba84e9ac3137b201f2ba605c6a7f6d4b10ac41941784f6.
def localCycle00021 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5]
    constant := ![-1, -3, 0, 0, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .triangle 24 1]

-- Cycle fingerprint 1fae4084bd33c90766f9c82635fb7263488646ebd90a767e56141f8cfa293131.
def localCycle00022 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 4, .distance 1 6, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 23 2, .gapLower 1 4, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 2018aa6c34b1ee73b6d248838c5c22f7943d995d1cdd424b86a86584f269c477.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 6]
    constant := ![0, -1, -1, 0, 1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 33 1, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 1, .triangle 15 2, .triangle 21 0]

-- Cycle fingerprint 202d56c7b75b0ab1bb85f81a0ec20a61d60a9a31a52604218dcf37839dd92b22.
def localCycle00024 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 21a795760c24caff04f392006c9df099aab4b60b7c42366c3d10aaa8c9a2269c.
def localCycle00025 : Cycle where
  length := 11
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6]
    constant := ![0, -1, 0, -1, 0, 0, -3, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 20 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 2242af9b32c1cf5639f72c1ebfcca5d28e8cbbacbdb4d3b76935095bc37c828f.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 3, .distance 1 6, .distance 0 6]
    constant := ![0, -1, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, true] }
  origin := ![.triangle 11 1, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 19 1, .gapLower 1 3, .triangle 4 2]

-- Cycle fingerprint 22b23dfda01bd896093fa63d30e2aa0371037a81d0efcfdf35a36774d64d1b87.
def localCycle00027 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 3, .distance 3 4, .distance 2 4]
    constant := ![0, -2, 0, -2, -1, -1, 0, 4, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 18 2, .gapLower 1 3, .triangle 20 0, .triangle 26 0, .gapLower 3 0, .gapLower 3 6, .triangle 25 2]

-- Cycle fingerprint 230f59f59f2bf39032e43048a1ed5937f9a44d58c03d631a64fecb7682292c9d.
def localCycle00028 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .gapLower 1 2]

-- Cycle fingerprint 231aeb1e58ead85d2acc4e35eec9404eb9ccd610cfa8e1f2762c94313d37bca5.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, -1, -2, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 235b1a58e468a7959d789b4fdb4506ebe2d7eb486e0edf0c7f711698655d530f.
def localCycle00030 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 6, .triangle 16 1, .triangle 15 2, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 2689eb3d6c3b990967e3f0f1c5127b78565ccae8af730d474e49ca38272b3864.
def localCycle00031 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 26e39e9ac3d2780672fb2933bfe9172194baf361eab2da94538052eb56b37fd6.
def localCycle00032 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 2 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 2, .distance 2 5, .distance 2 3, .theta 2, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![0, 0, -2, -2, 0, -1, 0, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, true, false, true, false, false, false, false, true, true] }
  origin := ![.triangle 27 2, .triangle 18 2, .gapLower 1 5, .gapLower 1 4, .triangle 0 2, .triangle 7 0, .triangle 26 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint 26f083c044276236091a2e3a4c5b9c04d4fff3b8082689ec3dd77f68874e830b.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 30 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 29c6d13d8f55a2cca20659c07709f1344e716b68258c5143b65e30fcf3c6d2ca.
def localCycle00034 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 0 2, .distance 2 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 0 2, .triangle 8 0, .triangle 27 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 2bc86880194e8c200f227673de0244963e9acc45773868db282958e135d98250.
def localCycle00035 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 5, .distance 3 5, .distance 2 5, .distance 4 5]
    constant := ![-1, 3, 0, 0, -2, 0, 0, -2, 0, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, true, true, true] }
  origin := ![.corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 15 2, .triangle 21 2, .gapLower 1 2, .triangle 3 2, .triangle 10 1, .triangle 26 2, .triangle 28 1]

-- Cycle fingerprint 2d6ab7617f891bb38290365399d667eb94fdb8a98383b032c7833c83e83fd35a.
def localCycle00036 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 20 1, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 2dbc9b1632262bf492897788cfab92c2669cf8a58ee8e7f3a1a6c92636859a5b.
def localCycle00037 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 2 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![0, 0, -2, 0, 0, -2, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, true, true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 16 1, .triangle 17 2, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint 2de7733255fa8413b0509e891f92d89596ee0462b51f923581730bf745517dbb.
def localCycle00038 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 18 0, .triangle 17 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 2e56298dc9a57cfa1f9f98e86d31d56ead4496be2e8ed855c76278ba811e4450.
def localCycle00039 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 8 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 2e5e0b1f472fe3e928c3d454d15014161b66d185197d753522f04da1cf7013e4.
def localCycle00040 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 2ecffb8960add64aafadecc0737f172496bdd8d5f42d6431ba1ae6e5f2b422e5.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![-1, -1, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 1, .gapLower 1 3, .triangle 1 2]

-- Cycle fingerprint 2f576fc2d7cf9bcff162812f0eda6d75d24c538e85f3d949798486b071d878ab.
def localCycle00042 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 6, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 6, .distance 2 6]
    constant := ![0, 0, -1, 3, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true, true, false, true, false, true, true] }
  origin := ![.triangle 29 1, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 15 2, .gapLower 1 3, .triangle 4 2, .triangle 8 1]

-- Cycle fingerprint 2fc52d79638e3bd59c488780db9bc1e7f929ea7ab3874339ab44669aa41542fa.
def localCycle00043 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 0 4, .distance 0 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.gapLower 1 6, .triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 303f529585f03c81ac187ee4d3034265a3e55c180d364fbfc0a05dac9aa08425.
def localCycle00044 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .triangle 24 1, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 3044d62f2de6d5521a12f0ac45f3c021439ebea69b70a4136eae6458502405cd.
def localCycle00045 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, 0, 0, -1, 0, 0, -3, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 16 0, .triangle 18 2, .triangle 21 1, .triangle 20 0, .gapLower 3 2, .gapLower 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 30b09e5ae5cbef405d67f89f3668cea46d53fa552ecb841768d3c694b1ca81cc.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 0 5, .distance 2 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![0, -3, 0, 0, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, true, true, false, false, true, false] }
  origin := ![.triangle 18 2, .gapLower 1 3, .triangle 3 2, .triangle 7 1, .triangle 28 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0]

-- Cycle fingerprint 31c2206412be8aafa78cbeead9f69e0a25752ac8f89e8fe08edf9d5aa5eaecd2.
def localCycle00047 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 3263f66f60639555d7f7ccbee43f3c822eb57899d7d919c1ace12dfaa927d81d.
def localCycle00048 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 33c3df96f5fff99743f2ac34cb945d3b997a306c5c508a01e0b0645a4fcf6956.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 2, .triangle 11 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 341ead759ce7e6e374fdca27124f70211f121ae1184c97bdd63e456832c9f507.
def localCycle00050 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 0 5, .distance 2 5, .distance 4 5, .theta 4, .distance 3 4]
    constant := ![0, -1, -2, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, true, false, false] }
  origin := ![.triangle 25 2, .triangle 16 0, .gapLower 1 3, .triangle 3 2, .triangle 7 1, .triangle 28 1, .corridorLower 4 5, .corridorUpper 3 4]

-- Cycle fingerprint 34b626f75704d985aec5547a88d8a981ab37eb73b30e1e2e129ae64c5da7eafd.
def localCycle00051 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 357eb6b0d6e9cce2cffc9f50600c3aca24692be7f113dea576f88fce9d659a57.
def localCycle00052 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 1 5]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 6 5, .triangle 24 0]

-- Cycle fingerprint 361e5ee71ffd1e6b80415644ec1ed2ed8203d3ad84e678055c8276df14da5517.
def localCycle00053 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 2, .distance 2 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 3, .gapLower 1 4, .gapUpper 2 4]

-- Cycle fingerprint 368688607a4f55fef005c94ef74ddecc34dc7693680f0e2837a6b8fcc54dc3ae.
def localCycle00054 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 4, .triangle 1 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 3694ec60383a7b1f3b2dec687ec90662fd8c12d9608ee3e2f4aa6ec3f92cc3c3.
def localCycle00055 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 18 2, .gapLower 1 3, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0]

-- Cycle fingerprint 37ef8e2ad95246a11b1068d1cf18458bb627e1b37d362544790d43707b1ebbf9.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 3, .distance 3 6]
    constant := ![0, -1, -1, 0, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 33 1, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 2 2, .triangle 9 1, .triangle 11 0]

-- Cycle fingerprint 39090d1454ce34807384891abff1753c920783ad20b024c61cdbce7083f2e087.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6]
    constant := ![0, -3, -1, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2]

-- Cycle fingerprint 3929f9edd2f55b4b64cd802e96a898e96485a1f5d20237932a90022d00f82100.
def localCycle00058 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 3, .distance 3 4, .distance 2 4]
    constant := ![0, -2, -2, 0, -1, -1, 0, 4, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 15 2, .triangle 20 0, .triangle 26 0, .gapLower 3 0, .gapLower 3 6, .triangle 25 2]

-- Cycle fingerprint 3ac46d0b1c3b5aa6b40710e9fea27caad9e987f2f98d67446c1072ba53b82f6e.
def localCycle00059 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5]
    constant := ![0, -1, -2, 0, 0, 3, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 20 1, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 3de6fdc035d7e8e603f805a7f980c2586784e29aa7cbad9e999b95197f33895f.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 18 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0]

-- Cycle fingerprint 3fb7730a2d2576af6c7e319e6afc034589b003a5106d6c7cdce029402545a9e2.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 3]
    constant := ![-1, -1, -1, 4, -1, -2, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.triangle 10 0, .triangle 26 0, .corridorLower 2 3, .gapLower 2 6, .triangle 16 0, .gapLower 1 4, .triangle 4 2, .triangle 11 1]

-- Cycle fingerprint 4172f0224f0f2e094175a572052864e71c765f4f0cbd96052c7c4025951c564f.
def localCycle00062 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 0 2, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 4336545a4bb5ebd11157b05ab8c584afa1a8784c802f48ff17e8e9c29eb30b6e.
def localCycle00063 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint 43fae809445ee3248bd2dcb9f9497bf004150fbc0fa10eae09555beb4ecd5405.
def localCycle00064 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 2, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 44375e4f4f104d8e6069ee562b8660ddfa30a1cdddbe8d00289e5987f7e5f5c8.
def localCycle00065 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 44a6cd717af98278136b8df93c892d7eb0e83dfa12368876181a47cfba3bf28d.
def localCycle00066 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 21 1, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 452010a98c9979a46bba4c231c0cafe1a9dc8f4b59b14daaaaab395212bf714b.
def localCycle00067 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 45b2b583eba08f2a4e4abd8713f90ba0fdf95e6b7f8e9f0385e006f494110d73.
def localCycle00068 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -1, 0, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 29 0, .triangle 13 0, .gapLower 0 4, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 46589df6f871bc14a74c393986b50342e62c9017eaebb28dca744aefc94546cf.
def localCycle00069 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4]
    constant := ![0, -1, 0, 0, -2, -2, 0, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, true, true, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 20 1, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0]

-- Cycle fingerprint 47630d6f79611af0010ea4cf57d90d545f85b8647477aec16822bb789a5811fa.
def localCycle00070 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 6 1, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 48b422755bef84bfeb4bd7c3de8e84172cdca26f9e6f033ca410b4d2908ed666.
def localCycle00071 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 4a823409b066a56b6a9ed33e03dbb171c7986b1755d554f5879312499e689e01.
def localCycle00072 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 2, .distance 0 2, .distance 2 6]
    constant := ![0, 0, -1, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, true, false, false, true, false] }
  origin := ![.triangle 30 1, .triangle 26 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 0 2, .triangle 8 0]

-- Cycle fingerprint 4adec26101df5af376d13e0b927c5e9c662b578a3f5260992c3a3dabc18a8d28.
def localCycle00073 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .distance 2 4, .distance 1 2, .distance 1 6]
    constant := ![-2, -1, -1, 0, 4, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 20 0, .triangle 26 0, .gapLower 2 0, .gapLower 2 6, .triangle 16 0, .triangle 18 2]

-- Cycle fingerprint 4c10d26bf0442ae8acff736dd2e12cd00d58b8f79e863212d1ad666c09451c20.
def localCycle00074 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 16 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 4c8eff572e1eeca8e66a96a983d03f4446079d66a09d86e2416ef061b67c88cc.
def localCycle00075 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 1 5]
    constant := ![2, 0, 0, -1, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 18 0, .gapLower 1 3, .triangle 20 2]

-- Cycle fingerprint 4c9a52d79e77d0baf669c8348c8ab7f7e4b389a9b624dcebcd6d95c3555ec6ae.
def localCycle00076 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -1, -1, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 17 2, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint 4e15553d791b78dcfde12ecbd58057e1319c417945ca4c8007bc5ec438f3a641.
def localCycle00077 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 1 3, .triangle 21 1]

-- Cycle fingerprint 4eeac1ffcc3cbd770ebe64ca2e5e6106e7269cd2a78ac0b319c42d76257b9a19.
def localCycle00078 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 1 4, .triangle 17 2, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1]

-- Cycle fingerprint 4effff7c4e01ce22b2100638d2bcee32e25ce659648a7f86062a628da2a13afe.
def localCycle00079 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 17 2, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 507a133824b0eb845636077d9722e7b75c88bbb44b8e21a8e5814ec88b86d1df.
def localCycle00080 : Cycle where
  length := 12
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6]
    constant := ![0, 0, 0, 0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 16 1, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 51603bb90c38db44fe7522690cf64a7c0a7b3c0578c6449a4657d95f18f3207b.
def localCycle00081 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .distance 2 4]
    constant := ![0, -2, 0, -2, 0, -1, -1, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.gapLower 4 4, .gapLower 1 5, .triangle 18 2, .gapLower 1 3, .triangle 1 2, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .gapLower 2 6]

-- Cycle fingerprint 51b14c48b48dbb846984c5a31ed77dbad6e80a6fad99d7bc728785777f61b82d.
def localCycle00082 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 5253d9673809e494b85abe26b5a24ba7d759acfd32886f9f4777f25a8da9cada.
def localCycle00083 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 543c50a9dff345ac94c155a811187015cd5477da7a3754c78411c461f8d41d7c.
def localCycle00084 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 29 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 5634b257387eb3771e4e69ce802a389555ee4cc8f8d66076c097439132262034.
def localCycle00085 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 8 0, .triangle 5 2, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 59f5f0bfe04ca15827c8ba3229f2a41f5f78c29240246fd4cce5af76cbafd61e.
def localCycle00086 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 1 5]
    constant := ![2, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 27 2, .triangle 18 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 5a40e5cfe838cf75ed89186c5a0afcb17e8f960f0d653f77128d8666b95beef7.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6]
    constant := ![0, 0, 0, 0, -1, 3, 0, -1, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, true, false, false, true, false, false] }
  origin := ![.triangle 4 2, .triangle 8 1, .triangle 29 1, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 4]

-- Cycle fingerprint 5c7f42b16b42e939b57b114c496891b10c503e50e98b7ee24163abaee388a040.
def localCycle00088 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 2 6, .distance 1 6, .distance 1 4, .distance 0 4, .distance 0 2, .distance 2 5, .distance 2 3, .theta 2, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![0, 0, -3, 0, 0, -1, 0, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, true, true, false, true, false, false, false, false, true, true] }
  origin := ![.triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 26 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint 5f22717d63be107dae5bbda4d2a4193393aec448c9d8ca8eadfb922e1139e735.
def localCycle00089 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 18 2, .gapLower 1 4, .triangle 17 2, .triangle 20 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 5fe643747ad66ead08adda477ade93c7976aaadce7576cbeaeae5dfb389202c0.
def localCycle00090 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 5 5]

-- Cycle fingerprint 608274e79a9033e6ad1d13bac0ea8c2abd7424a114e8dd33f73273ddf8f84345.
def localCycle00091 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 2 3, .theta 2, .distance 2 4, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 5]
    constant := ![-1, -1, 4, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 26 0, .corridorLower 2 3, .gapLower 2 6, .gapLower 4 4, .gapLower 1 5, .gapLower 1 4, .triangle 21 1, .triangle 20 0]

-- Cycle fingerprint 6086f865b098ade7de47b3c8615c34ac7f4006aed5e8cf2c5c2356eb15573da2.
def localCycle00092 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 4, .gapUpper 3 5, .gapLower 4 5, .triangle 16 0]

-- Cycle fingerprint 608c85bbf544360dbe495203b9fca58fee848914ebb2834b430c6975471a0daf.
def localCycle00093 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4]
    constant := ![-1, -3, 0, 0, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, true, true, true, false, false] }
  origin := ![.triangle 19 0, .gapLower 1 3, .triangle 4 2, .triangle 11 1, .triangle 27 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4]

-- Cycle fingerprint 61dcfcb9c2f2986b66a9d111a66c0f1fe297ebf0f3de64796242be9200f9dab2.
def localCycle00094 : Cycle where
  length := 4
  data := {
    node := ![.distance 5 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 5 6]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 33 2, .triangle 21 0, .gapLower 1 2, .gapUpper 5 5]

-- Cycle fingerprint 6211ee8f5fbfc1f639bb7b15e45e17b649c04dd8d39da73f165f99af6f2ad296.
def localCycle00095 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, -2, 0, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 1 4, .gapLower 1 3, .triangle 20 1, .triangle 1 0, .corridorLower 0 1]

-- Cycle fingerprint 625a7e1d7189c0b65d917a4fd47d70ec905d2d28868ed892ad0da6b7faf7bc33.
def localCycle00096 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 4, .distance 1 2, .distance 1 3, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 16 1, .gapLower 1 4, .triangle 1 2, .triangle 11 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 62cd2c67f0581505153557f4bd76f42f5a5cb849c4162a2d9a30de02665c9cfe.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 1 2, .distance 1 3, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .distance 2 4]
    constant := ![0, -2, 0, -2, 0, -1, -1, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.gapLower 4 4, .gapLower 1 5, .triangle 18 1, .gapLower 1 3, .triangle 1 2, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .gapLower 2 6]

-- Cycle fingerprint 630cf8786dfa976e20f346965b469237c26a09b83a1a1ab0b7ff663f487d1a75.
def localCycle00098 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -1, 0, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .triangle 24 1, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 634e3956362d483294bc356fd2c07668649325e1a5e4f57566ad0c1cfb5c8acc.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 5, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2, .distance 2 4]
    constant := ![-1, -2, 0, -2, 0, 0, -1, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.triangle 16 0, .gapLower 1 4, .triangle 21 1, .gapLower 1 2, .triangle 3 2, .triangle 10 1, .triangle 26 0, .corridorLower 2 3, .gapLower 2 6]

-- Cycle fingerprint 6371cbe49c11ba2369e5097a4b604be49752f612f6c866489cb164916989a6df.
def localCycle00100 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 2, .distance 1 6]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 18 2]

-- Cycle fingerprint 658f2885878e6880d0db27adb41d264bcc2e7e3b24f2a248ffe9be1e73ca537a.
def localCycle00101 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 6, .triangle 16 1, .triangle 15 2, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 664cada90931fcde9e57e60dba6d1c0c7c0e304150933588b6e4b12d834333bb.
def localCycle00102 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 685608eb152c8f27a5d4f1599ace7e6f9d39e4859b92f9f422b7d51d9cc00301.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 6, .distance 1 2, .distance 0 2]
    constant := ![-1, 0, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.triangle 7 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 23 2, .gapLower 1 4, .triangle 0 2]

-- Cycle fingerprint 6a6f9e36f568723fc4bf9f6aa4ac4266117635ca0e0cdbaff163ee523aeca34f.
def localCycle00104 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 6]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 6 5, .triangle 24 0, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint 6b1a19bd2f5dc920a4600f15349772931f427481fd83f9307f3926079519627d.
def localCycle00105 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 6c180d07378f87605504491981ec0e10cc5d16473c28befbcfae9804f92a868b.
def localCycle00106 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint 6d35eae047b57c01bac2b1b80df07d3907317d17c317ab957db765560a7c5930.
def localCycle00107 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-1, -1, -1, 0, 0, 3, 0, -1, -3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 70b9f3c2a6e008b141680dbab2ad422efe89f8086d80eab2ebde7388c3a57e78.
def localCycle00108 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4]
    constant := ![-1, -3, -1, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 16 0, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0]

-- Cycle fingerprint 7191860a6aef9b89f561701fa53da15f23725834b4836df8bae91ef4a3abbfcb.
def localCycle00109 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 6 1, .triangle 5 2, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 72346f27f96e7ee3c72351ec309726aeaf2db674927064ff5bff2c5fdcfe9d90.
def localCycle00110 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 1 3, .distance 1 6, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.gapLower 1 6, .triangle 19 1, .gapLower 1 3, .triangle 21 1, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 72d12a47cf8584d6055250bfcfcd544d2248c1147343215e1d1a6c6ccecda245.
def localCycle00111 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, -1, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint 749da69e16b75100e696b68d313d628d1316f966ac86a0678517de32fa0969a5.
def localCycle00112 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 74ac1ef8891c083a871e9d193fd0f8bc2b75bf0ee18988086cf88f477dbd1791.
def localCycle00113 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 4, .gapUpper 3 5, .gapLower 4 5, .triangle 16 0]

-- Cycle fingerprint 75bb79d5ec6a14ec6cae5b6ba397d39df59586c0a04827fc8aa8e2e1baa3ec48.
def localCycle00114 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 75d83e7b2ce52d62dd03ddaa2a2e76dd439202ff8e923a2c666317f0779387e6.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 8 0, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 75ff78cbf5643f32be505d29b3758a32e424e48c1eac199d38646f714fcbb08e.
def localCycle00116 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 4, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![0, 2, -2, 0, 0, 0, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 0 2, .triangle 8 2, .triangle 11 1, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 76c3c96f539bfd99a932e98108944748f04912c232132d2e08f2a6f2f1af3090.
def localCycle00117 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-1, -2, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint 76e1f219b07310a76b2d2c789ddbf2da790f2d81cb7407a631ca5ae12bdf58bc.
def localCycle00118 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .distance 2 4]
    constant := ![0, -2, -2, 0, 0, -1, -1, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 4 4, .gapLower 1 5, .gapLower 1 4, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .gapLower 2 6]

-- Cycle fingerprint 7a45f8295345592d9587fbac6959c8650bce4e0ecffc00fe58a50563e69d720d.
def localCycle00119 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 2 3, .theta 2, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 5]
    constant := ![-1, -1, 4, -1, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 26 0, .corridorLower 2 3, .gapLower 2 6, .triangle 16 0, .gapLower 1 4, .gapLower 1 3, .triangle 1 2, .triangle 10 0]

-- Cycle fingerprint 7bd59583abd37a7383d06a925c214aa310675a178ef817ee1e57fa601732797c.
def localCycle00120 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .triangle 17 1, .triangle 16 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Cycle fingerprint 80b1eaec4655f3b2505a662f77fb99e050891e340d7097cf4a2f4c3d217193b6.
def localCycle00121 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![0, 2, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false] }
  origin := ![.triangle 17 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 16 0]

-- Cycle fingerprint 80e2a4dc5ffc82d22deaa5154e28047c77a01b93f2dc6550fd5a7583a0c42fb9.
def localCycle00122 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 2, .distance 2 6]
    constant := ![0, 0, -1, 0, 1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, true, false, true, true, false] }
  origin := ![.triangle 30 1, .triangle 26 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 2 2, .triangle 6 1, .triangle 8 0]

-- Cycle fingerprint 83015d1cd697629494d859db5f8241e559eb5ba657cb67e9e1401459f8cce07f.
def localCycle00123 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 0 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 6, .triangle 2 2, .triangle 9 1, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 83147c986730ee1be8a5a42ef1f8a398511746709605173943ecd2c0e2f2ad82.
def localCycle00124 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 833afcee5456b98b03b68a3c5748bca445172caa42997b08d7ffe47752cbbd6d.
def localCycle00125 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 26 1, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 83c40cea4fd543ef580bc359a226ababf9116075ad483c78d019e061b07c9d9f.
def localCycle00126 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint 850698eb946858d5408331e2515dd6b10766da82334154de5043c20f74059969.
def localCycle00127 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6]
    constant := ![-3, 0, 0, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 15 2, .triangle 20 2, .gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .gapLower 6 3]

-- Cycle fingerprint 85129625b72f8ef64d0d4856f738eecb0e1eec64462def1a4ffa85d6ff2be003.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 3, .triangle 1 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 864796e1e1359bf6550f0a21904eaf943591ceb6d0898ddabc75c623b7806578.
def localCycle00129 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 865c0a087c0fc4f7a239f17be76af47dd5f8c46bbc2b864cdd1b104af8287395.
def localCycle00130 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 5]
    constant := ![0, -1, -1, 0, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 20 1, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 1, .triangle 18 2, .gapLower 1 2]

-- Cycle fingerprint 86dbe340c6b6ae3b3540d6bb4e8ec0e3ffbf68d9543585a0df91fd214d579520.
def localCycle00131 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 0 0]

-- Cycle fingerprint 897de0534a929bf55639e176e314a29b7f2b7e1d4717a9c5aa5a7bfcfb8d2ef0.
def localCycle00132 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![0, 1, 0, 0, 0, 0, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 2 2, .triangle 6 1, .triangle 8 2, .triangle 11 1, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 8a571c1addd595a6a4339aeec0693b92e2dfc8aec6aeede87382b71ddf3c0c5e.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -3, 0, -1, 0, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, true, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 21 1, .triangle 20 0, .triangle 26 2, .triangle 28 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 8cb74ec479211f84f1efdfd4640267960577b51d6941de392246648678e91c83.
def localCycle00134 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 1 2, .distance 1 3]
    constant := ![-2, 2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 21 2, .gapLower 1 4, .triangle 15 2]

-- Cycle fingerprint 8ddde691c6a5bf172b5ed1fc2ccd2f7accbff5091a989655d9519c0917b091bf.
def localCycle00135 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 8de5e396b88494c9b133cb05c7197e9b7b7a30888eae00f5256b5d22cf94aa10.
def localCycle00136 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 1, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 4 2, .triangle 8 1, .triangle 7 0, .triangle 28 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 8eba2a74d7d40c6fd94bffb66fbfc505546937860f6b8c78841cc944381a7068.
def localCycle00137 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-1, -1, -1, 0, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 18 2, .triangle 21 1]

-- Cycle fingerprint 8f94fcd780b50c0c97c5355a24c65a880214941a97ae155ed715d0afbfdc64e5.
def localCycle00138 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 9288ac78ce836c7a520f9b9325d411cf18a66af7c280077fe0943c057b239ce4.
def localCycle00139 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6]
    constant := ![0, -2, -2, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2]

-- Cycle fingerprint 95957bc5512b4b4a0238d04bfd5b89516e61825cdf29dec29557eedfd74f5a27.
def localCycle00140 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 5, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 1 2, .triangle 20 1]

-- Cycle fingerprint 9606a3f739b32997e40e2ba5c5451488ac679949851c3e8c1cb77981387b7f78.
def localCycle00141 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 26 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 968dfa9d10f961a9f0046706a28fbeac28978f1ddbc35463622efda303289e18.
def localCycle00142 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 1 5, .distance 1 3, .distance 3 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint 985cd8c2f2d93e1851058bd5b16ca9e3f9909f1fa5f2b0b0d9c050fd202b0971.
def localCycle00143 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 2, .distance 2 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 3, .gapLower 1 4, .gapUpper 2 4]

-- Cycle fingerprint 9883ab26c2f883dfdd0a4061d2af0c9fd5b6e527dade1ad4a0bbb2f0eada6536.
def localCycle00144 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 2 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![0, 0, -2, 0, 0, 0, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, true, true, true, false, false, false, false, false, true, true] }
  origin := ![.triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 16 1, .triangle 17 2, .triangle 20 1, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint 99190ef61ee87d7153d71afc6a17bee7c9c536e48b39da5f14d546e19d44ecf1.
def localCycle00145 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 9a05ec3c9c4b75c5623b2a8fe0b34fc48c934105ff6c50d481e085ca51103f12.
def localCycle00146 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint 9a8252f8bcb06e7c9fd2c2842cde93cc543596da29ffb315956ee9427fadead3.
def localCycle00147 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 6]
    constant := ![0, -1, -1, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, false] }
  origin := ![.triangle 33 1, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 15 2, .triangle 21 0]

-- Cycle fingerprint 9bcd5a22b494e1e4fe36d49d5f7ac90be810c20dfa92042d06036eed0435380c.
def localCycle00148 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 9c2f527a6c07a067310b6488c0d594eb62d5500b77a8cae446d8d2f8e65192d5.
def localCycle00149 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 9d214e139bc55c843c59401fd6c0b27c3dbb879e4ee086d7097c1b66289b85f3.
def localCycle00150 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-1, -1, -1, 0, 1, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 1, .triangle 18 2, .triangle 21 1]

-- Cycle fingerprint 9e01c433c933ed38db08ced3f49390ba586a8842ed01a70aebd148a3be13cb94.
def localCycle00151 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 2, .distance 2 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 4, .gapLower 1 5, .gapUpper 2 5]

-- Cycle fingerprint 9f09f503c1c4764a94772a6d493e589300c9e3d58f34a14b4637243153ddc674.
def localCycle00152 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![0, 0, -2, -1, 0, 0, 3, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 17 2, .triangle 20 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 16 0]

-- Cycle fingerprint 9fed30e379f547515c886220c7d40e42a8c406934c50996822c61ed43a06d25a.
def localCycle00153 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .distance 2 4]
    constant := ![0, -2, -2, 0, 0, -1, -1, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 4 4, .gapLower 1 5, .gapLower 1 4, .triangle 4 2, .triangle 11 1, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .gapLower 2 6]

-- Cycle fingerprint a02cde57ee5470eba11e6bc08660a7dc78ba95d481b5b086fdd2051217d015d3.
def localCycle00154 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 1 3]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .triangle 33 2, .triangle 21 0]

-- Cycle fingerprint a04cde79f6e0dcaa6f3495ac8dce1a9d275d1487b997deafdfcc8713d4c8eef2.
def localCycle00155 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 10 1, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint a057e104d9e154e2a10d50a26973f0d8ed4b84b11101de2f55eb7a4d87f66647.
def localCycle00156 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 4, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![0, 2, -2, 0, 0, -1, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, false, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint a0c1496baa8582c59383e4c0df87d2a6485f28899fcdbab86f216d475e9d631b.
def localCycle00157 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint a179fcb82e3433ac48064bfe3e554b8eefce5484667951b2620289758fc13bd4.
def localCycle00158 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint a278ea28188f9efeca46f4413b59c043e73cc91a83f63400f5b0f571f77df9d0.
def localCycle00159 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, -2, 0, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 16 1, .triangle 18 2, .gapLower 1 3, .triangle 1 2, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint a2ef511ab6bd370d560ba8fafbf679f87291bc0faa30d0a0aa5c333a11c9c375.
def localCycle00160 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint a492bc8a5735d25398281e7223ae204e8ba039be1c8183a2da5d9440f60a7d5b.
def localCycle00161 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint a4e505c47f4af8ec3997afa382a7442951ac1d37e7b2f1cfe511be37b38be0a9.
def localCycle00162 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, 0, -1, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 18 1, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 1 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint a4f92db99d01c5f146eaab8c359a0b784a756fbd14285d5de880895032cc05cb.
def localCycle00163 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5]
    constant := ![0, -3, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0]

-- Cycle fingerprint a5ddea5ad624a38ef2883de8b91527a1f751ee348dcfce09bc456c7dfd6cf32d.
def localCycle00164 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 3, .distance 3 6]
    constant := ![0, -1, -1, 0, 1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 33 1, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 2 2, .triangle 9 1, .triangle 11 0]

-- Cycle fingerprint a6a32800c0d29f62dbeb82dc62653ee5ba1640d44b915d6f17307f3ce952a4dc.
def localCycle00165 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 1 3]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 21 0]

-- Cycle fingerprint a77718cb5c484f5903d8a1981aae50656a247eea736626e85b7c977cd2db0fd4.
def localCycle00166 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 0, .gapLower 1 4, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint a7b47ad9f2593470f531d62cea1ee6727007833f096e069e8439605131021d91.
def localCycle00167 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 2, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint a9424aa6efecefc473a4bca8b1dbd5859a19e469de6414565599059d85eccde7.
def localCycle00168 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .theta 2, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 2 3]
    constant := ![-1, 0, 0, 3, 0, -1, -3, 0, 0, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, false, false] }
  origin := ![.corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 4, .triangle 4 2, .triangle 11 1, .triangle 10 0, .triangle 26 0]

-- Cycle fingerprint ab0f397e1b248eb7b31c71733896b0bc7deca986bec3eacdd5d3e8f8134a7fed.
def localCycle00169 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, 0, 0, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 2 2, .triangle 6 1, .triangle 8 2, .triangle 11 1, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint abf4e6aaa081becc089bfbf7b567f10d5e2e819c7a38342129efe7bd1ef01cfb.
def localCycle00170 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint ac5aca0c0cffb402b1bec8862a4072bbf895060e10df85b13fa4bb82257e674b.
def localCycle00171 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -3, 0, 0, 0, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, true, true, false, false, true] }
  origin := ![.triangle 16 0, .gapLower 1 4, .triangle 4 2, .triangle 8 1, .triangle 29 1, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint ac9f786989839b41d40741152829fbc122ed97c74e58be9aac8be73540f7511a.
def localCycle00172 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 6]
    constant := ![0, -1, -1, 0, 2, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 33 1, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 1, .gapLower 1 4, .triangle 21 0]

-- Cycle fingerprint acb2d505f86e3ad23e38c9028fe087c5ee3a582873cd574ffd3b0ade54290ba1.
def localCycle00173 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint acd91d3e932e218138ea95dc326dbc5dfba640de9a578a043e2b2f5f07b51344.
def localCycle00174 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 0 2, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint afb2a2ea564e4d23800b1fd38290b0f154270b5e980bb64acaffd588b769a48a.
def localCycle00175 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 2, .triangle 6 1, .triangle 5 2, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint b0b12b393ac63663242bbcb75a4feab9fad278c8e3d63b97e7c57876ccc4aadb.
def localCycle00176 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -1, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .triangle 24 1, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint b0b5749a630f0ec269c964cdda0959968693f5918becda483fe343c925463745.
def localCycle00177 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 27 0, .gapLower 3 0]

-- Cycle fingerprint b0c92ec97c3c9a3fdc3a3ccd1f74e10c67b7ca8aeee6a6568d557f8d09a72334.
def localCycle00178 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 18 1]

-- Cycle fingerprint b16ab281589aa6d919ae2eec9b464ee0c13852c5f9675f9e18ef6cbe94f587a6.
def localCycle00179 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 6, .distance 0 6, .distance 0 3]
    constant := ![-1, -1, -1, 0, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 4 2, .triangle 11 1]

-- Cycle fingerprint b2adc7710e25403ba685114b7712c0e8aecb1d67c80a1411cb18de83b2d8f7f8.
def localCycle00180 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 16 0, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint b2b6266edb92e2a2af1b577c008da24c28807ae113fe5db1dc75d93b186e958f.
def localCycle00181 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint b314d4e3d44f81cff771d54999a8f68ed4c61c4776900b820652502bb6f61418.
def localCycle00182 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 6 1, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint b3824647365d172c2695d7b29cb20002cb683f8e0f6865a8dbcb5eea86979d3a.
def localCycle00183 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 16 0, .triangle 29 0, .triangle 13 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint b5f6b4461ca4055e7705988327d92280c3023bcd6010d35ee15e8a44e57ae5a3.
def localCycle00184 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 6, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint b6fd8f5ad6f13f9fbb262df0d17808a17b650d0313527a34fc7f03e7b94b552f.
def localCycle00185 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 18 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint b9aa3f909124bc1d950cb22a7bd6b2b98f840a0b874e01a143dde92fc8ce1f1e.
def localCycle00186 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 0 3]
    constant := ![0, -3, 0, 0, 3, -1, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .gapLower 3 2]

-- Cycle fingerprint b9b49d865886fca96b7bf3d06b3e5911efed76695c610bf92fb278dc6704379a.
def localCycle00187 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint b9d738eb9deb46b76fbbe83e3d498af3405228a84316da7fdbc5d29b2bcdc425.
def localCycle00188 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint b9e1a0cf4ec40520b8cdb3de65340db95ccf6cb2b032c49ebb257dae4ff745db.
def localCycle00189 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .distance 2 4, .distance 1 2, .distance 1 6]
    constant := ![-2, -1, -1, -1, 4, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .gapLower 2 6, .triangle 16 0, .triangle 18 2]

-- Cycle fingerprint bb0c4604c1ff2f5a6439d7852b0454e86daa3a4f8eba5daefc940b023de28a77.
def localCycle00190 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 0 1, .theta 0, .zero, .theta 1, .distance 1 4, .distance 1 6]
    constant := ![-1, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint bf0ede200e500c9374e8b5ed8e44c370897708885899b0247685d053a451c6e2.
def localCycle00191 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 6 1, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint bfbc5a7a8e9b96b69cbbd56824058a3bb0697599af65e25edf7e97c5b6e42026.
def localCycle00192 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 5, .distance 2 5]
    constant := ![0, -1, 3, -1, -2, -2, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true] }
  origin := ![.triangle 28 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .gapLower 1 2, .triangle 3 2, .triangle 7 1]

-- Cycle fingerprint c0bb47595e2c2f1d4c30e6886fa497d866250fc978231fc6baad406bace52dc9.
def localCycle00193 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 5, .gapLower 4 5, .gapLower 4 4, .gapLower 1 5, .triangle 15 2]

-- Cycle fingerprint c2723d68386bfb089760d23192fa4f309a439405241451013de3d08d5baf83b5.
def localCycle00194 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 1 2, .distance 1 3]
    constant := ![0, 2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, false] }
  origin := ![.triangle 20 2, .gapUpper 5 5, .gapLower 6 5, .triangle 21 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint c3fd8164e987bddffd4f595c33ea128ea21e13f7ce778fde9a501d59602220e5.
def localCycle00195 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6]
    constant := ![-1, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint c5346f8b0f9960161d72b357feb48ba970ceb6746f7945a689c2bdb0a89dea71.
def localCycle00196 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 17 1, .triangle 16 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint c55cdfe2403613308600deaf75f6517b3e5e972797fb4f295adc5be4ea85375f.
def localCycle00197 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint c594afe28d4d8ac8f9b673788e8cd8bc47f7b649c8ff03fd8a2d275721ba759d.
def localCycle00198 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 1 3]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 21 0]

-- Cycle fingerprint c684264228fba1f09b949006f5a143b57fe356d49149cdcd44bea00e74839674.
def localCycle00199 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 2 3, .theta 2, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 5, .distance 3 5]
    constant := ![-1, -1, 4, -1, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 26 0, .corridorLower 2 3, .gapLower 2 6, .triangle 16 0, .gapLower 1 4, .triangle 21 1, .gapLower 1 2, .triangle 20 1]

-- Cycle fingerprint c6d8538dfcc9066c3bb0a9914ff157efac0f7d3d453b1499438db070849a6b5d.
def localCycle00200 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 1 6, .distance 1 4, .distance 0 4, .distance 0 2]
    constant := ![-1, 0, -1, 0, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.triangle 7 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 2 2, .triangle 6 1]

-- Cycle fingerprint c6e63f29f7bd6a40e68255715263b9ce0420515573ffa643ba9a3904b933244d.
def localCycle00201 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 0, .gapLower 1 4, .triangle 21 1, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint c93b171fce452fad9df03d2cec4af95b75aa11462f1b48986123273049b635e4.
def localCycle00202 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 0 2, .triangle 5 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Cycle fingerprint c9d27ef1693da5337356923fa0b484c5a88d48c08de6cdd8b98a5cc9139d77b2.
def localCycle00203 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -2, 0, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 18 2, .triangle 24 1, .triangle 20 1, .gapLower 1 1]

-- Cycle fingerprint c9f6acf5bc1064e696954fe1e9993035e823961351d4b0974fe3b43b111032ca.
def localCycle00204 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -3, 0, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, true, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 4 2, .triangle 8 1, .triangle 7 0, .triangle 28 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint cb791f0433f1088c69fe95be92fe57ca00bd5304fa03e2dd621445eb4deb95e2.
def localCycle00205 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -1, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .triangle 21 1, .gapLower 1 2, .triangle 3 0]

-- Cycle fingerprint cc6426ce8942acc638094a398e75b3b290cd2489646b93eafc46d44ede83bb0f.
def localCycle00206 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 0 5, .distance 2 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5]
    constant := ![0, 0, 0, -1, 3, 0, -1, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, true, false, true, false] }
  origin := ![.triangle 3 2, .triangle 7 1, .triangle 28 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 1 3]

-- Cycle fingerprint ccb3dcfb0b0aa930cab54107ab877aeafdf9e59433a3d5d701173342af28de66.
def localCycle00207 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 16 0, .triangle 29 0, .triangle 34 1, .triangle 14 0, .triangle 7 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint ccec8d789ee51b689b3d47f640c1bb6dd9fb6ee3dede9334201b580debd1302d.
def localCycle00208 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 5, .distance 2 3]
    constant := ![-1, 4, -1, 0, -2, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.corridorLower 2 3, .gapLower 2 6, .triangle 16 0, .triangle 18 2, .gapLower 1 3, .triangle 1 2, .triangle 10 0, .triangle 26 0]

-- Cycle fingerprint cd0780c512c7bb06412fd99487540bef7a3fe02aded361eb168cabbcf0d50d97.
def localCycle00209 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 18 2, .gapLower 1 2, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0]

-- Cycle fingerprint d0459fd26423cabf109f314a75f29cb48e1bed456061e5eaa8a2328caecec336.
def localCycle00210 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 5, .distance 2 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 5]
    constant := ![0, 0, -1, 3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true, true, false, true, true, false, true] }
  origin := ![.triangle 7 1, .triangle 28 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 15 2, .triangle 21 2, .gapLower 1 2, .triangle 3 2]

-- Cycle fingerprint d04a01d5a852c2ee29a1cbf9e2928cd3f715816b78eb47e09ef46c1052b44a01.
def localCycle00211 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 6, .distance 1 2, .distance 1 3]
    constant := ![-1, -1, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 23 2, .gapLower 1 4, .triangle 15 2]

-- Cycle fingerprint d11319bcf5aa71cce6815f4862d84f86daf3ee6f92e69f5c9f8595001f1cb5e9.
def localCycle00212 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 23 2, .gapLower 1 4, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2]

-- Cycle fingerprint d19ed8ed589c29cabf9cf321132c031117d4c6015f18c7ece2edbe5f60aecaf5.
def localCycle00213 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6]
    constant := ![3, -1, -1, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .triangle 1 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint d3d4372bbe2d08c178faff762d41a266d949ad2c9e63e864f930c90fdc4d0318.
def localCycle00214 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6]
    constant := ![-2, 0, -2, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 15 2, .gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 18 2]

-- Cycle fingerprint d3e82eaca0cada213f96689a5db4509e4db1e9abda14a25ef83f817329abd2e6.
def localCycle00215 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-1, -1, -1, 0, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 1, .triangle 18 2, .gapLower 1 3]

-- Cycle fingerprint d69a1538bde2d308f9656a64ee0711d68dae84bedcd0b45917bbc4e649ca64bc.
def localCycle00216 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 0 5, .distance 2 5, .distance 4 5]
    constant := ![-1, 3, 0, -1, -3, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true] }
  origin := ![.corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 3, .triangle 3 2, .triangle 7 1, .triangle 28 1]

-- Cycle fingerprint d7931389e17c9d43bffce3a8910c86c057142abee0570370220cce04a3d09979.
def localCycle00217 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint d7ec84da5800cfc84971d43c5e07360e008ce90d5b12657cb5f80dda1a514484.
def localCycle00218 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint d890deea1f5e20cf319ee8af2a979574fc94caad0062702df76b1a372ffdfd5e.
def localCycle00219 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 6]
    constant := ![0, -1, -1, 0, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 33 1, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 1, .triangle 15 2, .triangle 21 0]

-- Cycle fingerprint d8d6d3670ec9de826e1e2c9e0c2ab0d647fc7f04911ab4bb63c254de8014cbbb.
def localCycle00220 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 17 2, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0]

-- Cycle fingerprint d9b490ae15c4ed10c80dd06853f04da26db025438d3d00ccd3f5e1e3bf4571f8.
def localCycle00221 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint da58a175bede7acf9ee3dbe920177d39fcf34b0bc7484413154340a31f3b04b8.
def localCycle00222 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, -1, 0, -1, -3, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint da8104f05aedbe4ed1f580c12cfb91b59a10631a5564952788f87b6a5034a31c.
def localCycle00223 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint dc330d0e26d27779d31d5fe8f622719b7db9ca2f63a0072a6d953d16003fa4b3.
def localCycle00224 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -2, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 18 2, .triangle 24 1, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint dc37bd423a9af4d08d5d312d60df6da172b157269eed86187402085c3b2fbb12.
def localCycle00225 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 0 2, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint dcbccf0f95fde8a444f9abdfccf746d38696192c79bfd33604e347eed075fdfc.
def localCycle00226 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint dd0d7f94bd0917804da09fe0cf5101d0de59caa48f1ba281ba78ce5df8dc3ff5.
def localCycle00227 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4]
    constant := ![3, 0, -1, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4]

-- Cycle fingerprint dd0ff7313879b2eafa3f9f66052f13236ec4bb628389f6170bd4e5af2ef9ca1e.
def localCycle00228 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint df8e0b16f5ceea806f8a8167bb403ce39d85c8a95b81a6477c2f537b817e2538.
def localCycle00229 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 0, .gapLower 1 3, .triangle 20 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint e031c7daa302223b6e911ab67c86db8e30dbb847d2227016d791777fa712783e.
def localCycle00230 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint e31c43fffab8b5277590c716abd91f49e547bd86f107107b4f2385ce463dcda1.
def localCycle00231 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 0 2, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint e34851403b6b8dc4d689f77f2cce8c1c08dfb88da93df81d729f20571b1bc827.
def localCycle00232 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 5]
    constant := ![0, 0, -1, 3, 0, 0, -2, 0, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true, true, false, true, true, true, false] }
  origin := ![.triangle 26 2, .triangle 28 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 0 2, .triangle 8 2, .triangle 11 1, .triangle 10 0]

-- Cycle fingerprint e453da6aa5fccb9e97f3eab0541e1bc95a9d759528a958d3d3ed808485a8e6d5.
def localCycle00233 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 0, 3, 0, -1, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint e47848a6a1f97dbec2fc884e49c1e951ceb92634ad8f5dbb7c5e35f3cf3da05a.
def localCycle00234 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 2, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint e68c3472a7283f9068120a606fd0efe6529f7140054a38ddd43f5bd557c343de.
def localCycle00235 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 1 5]
    constant := ![2, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 18 0, .gapLower 1 3, .triangle 20 2]

-- Cycle fingerprint e86b3e2af867d8d9c4561b22bf5f0331dd859e9a29a667604c2912d63ea25e8e.
def localCycle00236 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6]
    constant := ![-2, 0, 0, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 15 2, .triangle 20 2, .gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 18 2]

-- Cycle fingerprint e887c88e9425963fba93564549d1e68536ba3460593b0dd77973e950c0d4b18c.
def localCycle00237 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 16 0, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0]

-- Cycle fingerprint e9ba99f3b913d37dc900040b99e049257e7d7e68eafdd96ef9442dc5650c8e96.
def localCycle00238 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 0, .gapLower 1 4, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint ea12b65d977b05ee1e450724a23aa62ede21e7e63e8d22ee1b900005e14fa0ea.
def localCycle00239 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4]
    constant := ![-1, 0, 0, -1, -3, 0, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 16 0, .triangle 17 2, .triangle 20 1, .triangle 1 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 2]

-- Cycle fingerprint ea215407c1010c8ce1bbfc48f35c8c40004eefaade2bc3cc578ba7b3b70bac0a.
def localCycle00240 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint eae8a1043e022c9cd01a265c9aa1ff051e62a2cdadc344b69491cf347fec1935.
def localCycle00241 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .distance 4 6, .distance 4 5]
    constant := ![-1, 3, 0, 0, -2, 0, -2, 0, 0, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, true, true, true] }
  origin := ![.corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 15 2, .gapLower 1 3, .triangle 4 2, .triangle 11 1, .triangle 27 2, .triangle 29 1, .triangle 34 1]

-- Cycle fingerprint eb0733ef2340780e04584639d254444d8989bb7c2402b55ae66c85d11c45d533.
def localCycle00242 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint eb59fdb9a5dcd647b4aa95d5421fe181446f4a7e880605d431ba934408f337c9.
def localCycle00243 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .distance 2 4, .distance 1 2]
    constant := ![-2, -2, -1, -1, -1, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .gapLower 2 6, .triangle 16 0]

-- Cycle fingerprint ebfd76ae3e3adaa1042c1224826199d9c7587106ee3e9890481b485b314add19.
def localCycle00244 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0]

-- Cycle fingerprint ed0072c9d8c8eb899ee6b586c5aa5755a646ad2fc443fb78319af4dca33d8857.
def localCycle00245 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 1 5]
    constant := ![-1, -1, 0, 0, 3, 0, -1, -1, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .gapLower 1 3]

-- Cycle fingerprint edfa80ae467c0373e1db4007a36a6bae167be311c614710ca727f38c671d2ed7.
def localCycle00246 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, -2, 0, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 16 1, .triangle 18 2, .gapLower 1 2, .triangle 3 2, .triangle 10 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint efa35e33546f79c3149dd53e2e7507bbe5a20ad5233ebdf167d5a37b15ce11b5.
def localCycle00247 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-1, -3, 0, 0, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .triangle 21 1]

-- Cycle fingerprint f0d230c19d647462804039d5e115fca0a8d3d91e9e892c3a265be4e340cc20d0.
def localCycle00248 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint f3b8d5dce9056c6979f8d2bc897e92453e2f811368d04bb8a87c7b72ebd4d086.
def localCycle00249 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 2]
    constant := ![-1, 0, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.triangle 7 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 23 1, .gapLower 1 4, .triangle 0 2]

-- Cycle fingerprint f6a53982625753bc7289c1929fbfeb2e863ea2802a7ecc7afe720640891648e7.
def localCycle00250 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 16 0, .gapLower 1 3, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint f761b6e74b317629273eb01b4a2407ea7c4c1ec5de7c481375810ea871f733fb.
def localCycle00251 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 0 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 6, .triangle 2 2, .triangle 9 1, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint f9a8e26001c2ea9ecbc2c7b1b043cbc447360863ac3e132b283e32a33ed4bc9e.
def localCycle00252 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint f9d98cc6efcd710320f1ac47fee71d6f2345ffea9769bb159e85f8eb551d7e2d.
def localCycle00253 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint fa66336ec63eb2930b2eb70ad8bb497b478820318debc9990b81b91fcc56c767.
def localCycle00254 : Cycle where
  length := 12
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6]
    constant := ![0, -1, 0, 0, -2, 0, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 16 2, .gapLower 1 4, .triangle 17 2, .triangle 20 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint fa7fb3d4b3df7e906a011c891d1a904ef86b73285e75c1eb5c8adf1052fa7595.
def localCycle00255 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint faa80b8a59605ac5701eb8f850fafe4ee9c55d2bffea57cd3526671da5b99158.
def localCycle00256 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .triangle 24 1, .triangle 3 0, .gapLower 1 0]

-- Cycle fingerprint fb22dd36d0cd41cb47ac1fa80d5745f7ae90e2af184ea29937cbdbea3d8a1c8f.
def localCycle00257 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 23 0, .triangle 16 1, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint fb3b26925cc1011aa8a049a5d29c214017978ac02f2b3b5942ed00eb3f81e295.
def localCycle00258 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 3 5, .gapLower 4 5, .triangle 16 2, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint fb713879070caf61ee58723bc06055bac0eddd9edfcc3e9965a51d404a49f6df.
def localCycle00259 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint fbabc7c3afee4b3b8ebe73d7a21a9ce47c1f1d007a7ac13577b938f214ed06aa.
def localCycle00260 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint fc9a3d7f423c672317603fa6359bbc1b7f259f2d935f50788f34b5f49d42b1c0.
def localCycle00261 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 15 2, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint fd230dfed9510385af7cbea56e1ccff3e49576fbb5fdffd37448285663315c4c.
def localCycle00262 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint fde692a039f510518bbcc5e51d6563c0be6d6f33369a99a248704c1633eb1c2a.
def localCycle00263 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 1 2, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, -2, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, true, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 0 2, .triangle 7 0, .triangle 28 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint ffe738d541fc223afd924d600db7949b5258e2416e2bf58e13084632867f1dc7.
def localCycle00264 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 26 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

def library : Library := fun id => if id < 132 then (if id < 66 then (if id < 33 then (if id < 16 then (if id < 8 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none)))) else (if id < 12 then (if id < 10 then (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none)) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))) else (if id < 14 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none))))) else (if id < 24 then (if id < 20 then (if id < 18 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none))) else (if id < 22 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))) else (if id < 28 then (if id < 26 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 30 then (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))))))) else (if id < 49 then (if id < 41 then (if id < 37 then (if id < 35 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))) else (if id < 39 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)))) else (if id < 45 then (if id < 43 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))) else (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none))))) else (if id < 57 then (if id < 53 then (if id < 51 then (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none)) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none))) else (if id < 55 then (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)))) else (if id < 61 then (if id < 59 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none)) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))) else (if id < 63 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)))))))) else (if id < 99 then (if id < 82 then (if id < 74 then (if id < 70 then (if id < 68 then (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none))) else (if id < 72 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)))) else (if id < 78 then (if id < 76 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))) else (if id < 80 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none))))) else (if id < 90 then (if id < 86 then (if id < 84 then (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none))) else (if id < 88 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)))) else (if id < 94 then (if id < 92 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none))) else (if id < 96 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none))))))) else (if id < 115 then (if id < 107 then (if id < 103 then (if id < 101 then (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none))) else (if id < 105 then (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)))) else (if id < 111 then (if id < 109 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none))) else (if id < 113 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none)) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none))))) else (if id < 123 then (if id < 119 then (if id < 117 then (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none))) else (if id < 121 then (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none)) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none)))) else (if id < 127 then (if id < 125 then (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none))) else (if id < 129 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none))))))))) else (if id < 198 then (if id < 165 then (if id < 148 then (if id < 140 then (if id < 136 then (if id < 134 then (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none)) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none))) else (if id < 138 then (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none)) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)))) else (if id < 144 then (if id < 142 then (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none)) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none))) else (if id < 146 then (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none)) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none))))) else (if id < 156 then (if id < 152 then (if id < 150 then (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none)) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none))) else (if id < 154 then (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none)) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none)))) else (if id < 160 then (if id < 158 then (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none)) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none))) else (if id < 162 then (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none)) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none))))))) else (if id < 181 then (if id < 173 then (if id < 169 then (if id < 167 then (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none)) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none))) else (if id < 171 then (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none)) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none)))) else (if id < 177 then (if id < 175 then (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none)) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none))) else (if id < 179 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id = 178 then some localCycle00178 else none)) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none))))) else (if id < 189 then (if id < 185 then (if id < 183 then (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none)) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none))) else (if id < 187 then (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none)))) else (if id < 193 then (if id < 191 then (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none)) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none))) else (if id < 195 then (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none)) else (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none)))))))) else (if id < 231 then (if id < 214 then (if id < 206 then (if id < 202 then (if id < 200 then (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none)) else (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none))) else (if id < 204 then (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id = 203 then some localCycle00203 else none)) else (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none)))) else (if id < 210 then (if id < 208 then (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none)) else (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none))) else (if id < 212 then (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id = 211 then some localCycle00211 else none)) else (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id = 213 then some localCycle00213 else none))))) else (if id < 222 then (if id < 218 then (if id < 216 then (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none)) else (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id = 217 then some localCycle00217 else none))) else (if id < 220 then (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id = 219 then some localCycle00219 else none)) else (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id = 221 then some localCycle00221 else none)))) else (if id < 226 then (if id < 224 then (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id = 223 then some localCycle00223 else none)) else (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id = 225 then some localCycle00225 else none))) else (if id < 228 then (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id = 227 then some localCycle00227 else none)) else (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id = 230 then some localCycle00230 else none))))))) else (if id < 248 then (if id < 239 then (if id < 235 then (if id < 233 then (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id = 232 then some localCycle00232 else none)) else (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id = 234 then some localCycle00234 else none))) else (if id < 237 then (if id < 236 then (if id = 235 then some localCycle00235 else none) else (if id = 236 then some localCycle00236 else none)) else (if id < 238 then (if id = 237 then some localCycle00237 else none) else (if id = 238 then some localCycle00238 else none)))) else (if id < 243 then (if id < 241 then (if id < 240 then (if id = 239 then some localCycle00239 else none) else (if id = 240 then some localCycle00240 else none)) else (if id < 242 then (if id = 241 then some localCycle00241 else none) else (if id = 242 then some localCycle00242 else none))) else (if id < 245 then (if id < 244 then (if id = 243 then some localCycle00243 else none) else (if id = 244 then some localCycle00244 else none)) else (if id < 246 then (if id = 245 then some localCycle00245 else none) else (if id < 247 then (if id = 246 then some localCycle00246 else none) else (if id = 247 then some localCycle00247 else none)))))) else (if id < 256 then (if id < 252 then (if id < 250 then (if id < 249 then (if id = 248 then some localCycle00248 else none) else (if id = 249 then some localCycle00249 else none)) else (if id < 251 then (if id = 250 then some localCycle00250 else none) else (if id = 251 then some localCycle00251 else none))) else (if id < 254 then (if id < 253 then (if id = 252 then some localCycle00252 else none) else (if id = 253 then some localCycle00253 else none)) else (if id < 255 then (if id = 254 then some localCycle00254 else none) else (if id = 255 then some localCycle00255 else none)))) else (if id < 260 then (if id < 258 then (if id < 257 then (if id = 256 then some localCycle00256 else none) else (if id = 257 then some localCycle00257 else none)) else (if id < 259 then (if id = 258 then some localCycle00258 else none) else (if id = 259 then some localCycle00259 else none))) else (if id < 262 then (if id < 261 then (if id = 260 then some localCycle00260 else none) else (if id = 261 then some localCycle00261 else none)) else (if id < 263 then (if id = 262 then some localCycle00262 else none) else (if id < 264 then (if id = 263 then some localCycle00263 else none) else (if id = 264 then some localCycle00264 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 5, 3, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 6, 0, 5, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 3, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 177 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4608)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 5, 3, 2, 4], ![6, 3, 0, 5, 1, 4], ![6, 2, 0, 5, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 3, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 112 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4609)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 3, 5, 2, 4, 6], ![3, 5, 0, 1, 4, 6], ![2, 0, 1, 5, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 2, 0, 1, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .low (![239, 25, 142, 108, 53, 88, 136, 69, 76, 237, 17, 144, 184, 9, 111, 254, 4, 152, 1, 2, 37, 79, 167, 80, 245, 32, 249, 200]) }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4610)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 3, 5, 2, 4, 6], ![3, 5, 0, 1, 4, 6], ![2, 0, 1, 5, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 2, 0, 1, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 225 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4611)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 3, 5, 2, 4, 6], ![3, 5, 0, 1, 4, 6], ![2, 0, 1, 6, 5, 4], ![5, 0, 1, 2, 6, 3], ![4, 2, 0, 1, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 174 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4612)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 3, 5, 2, 4, 6], ![3, 5, 0, 1, 6, 4], ![2, 0, 1, 5, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 2, 0, 1, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 12 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4613)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 3, 5, 2, 6, 4], ![3, 5, 0, 1, 6, 4], ![2, 0, 1, 5, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 0, 1, 3, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 182 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4614)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 3, 5, 6, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 1, 5, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 0, 1, 3, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 8 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4615)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 3, 5, 2, 4, 6], ![3, 5, 0, 1, 6, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 1, 6, 2, 3], ![4, 2, 0, 1, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 83 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4616)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 3, 5, 2, 6, 4], ![3, 5, 0, 1, 6, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 0, 1, 6, 3], ![0, 4, 1, 2, 5, 3]], proof := .tail 191 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4617)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 3, 5, 6, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 0, 1, 6, 3], ![0, 4, 2, 1, 5, 3]], proof := .tail 8 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4618)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 3, 6, 5, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 0, 6, 1, 3], ![0, 4, 2, 5, 1, 3]], proof := .tail 33 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4619)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 6, 3, 5, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 6, 1, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 0, 6, 1, 3], ![0, 4, 2, 5, 3, 1]], proof := .tail 36 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4620)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 3, 5, 2, 6, 4], ![0, 3, 5, 2, 6, 4], ![3, 5, 0, 1, 6, 4], ![2, 0, 1, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 1, 3, 6], ![4, 0, 1, 2, 3, 5]], proof := .low (![213, 244, 142, 216, 143, 204, 43, 170, 220, 158, 212, 185, 63, 38, 229, 89, 181, 221, 250, 78, 126, 28, 95, 178, 50, 263, 103, 190]) }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4621)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 3, 5, 2, 6, 4], ![0, 3, 5, 2, 6, 4], ![3, 5, 0, 1, 6, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 1, 6, 3], ![4, 0, 1, 2, 5, 3]], proof := .tail 62 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4622)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 3, 5, 2, 6, 4], ![0, 3, 5, 6, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 1, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 1, 3, 6], ![4, 0, 2, 1, 3, 5]], proof := .tail 8 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4623)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 3, 5, 2, 6, 4], ![0, 3, 5, 6, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 1, 6, 3], ![4, 0, 2, 1, 5, 3]], proof := .tail 8 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4624)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 3, 5, 2, 6, 4], ![0, 3, 6, 5, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 6, 1, 3], ![4, 0, 2, 5, 1, 3]], proof := .tail 33 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4625)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 3, 5, 2, 6, 4], ![0, 6, 3, 5, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 6, 1, 3], ![4, 0, 2, 5, 3, 1]], proof := .tail 36 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4626)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 3, 5, 6, 2, 4], ![0, 3, 5, 6, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 0, 1, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 1, 3, 6], ![4, 2, 0, 1, 3, 5]], proof := .low (![213, 244, 142, 46, 171, 151, 122, 170, 176, 117, 59, 138, 63, 98, 106, 166, 203, 221, 149, 157, 224, 44, 180, 100, 206, 234, 87, 72]) }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4627)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 3, 5, 6, 2, 4], ![0, 3, 5, 6, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 1, 6, 3], ![4, 2, 0, 1, 5, 3]], proof := .low (![222, 163, 52, 217, 171, 151, 122, 233, 230, 117, 59, 138, 63, 195, 106, 166, 203, 48, 149, 157, 104, 104, 180, 100, 206, 234, 87, 72]) }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4628)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 3, 5, 6, 2, 4], ![0, 3, 6, 5, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 6, 1, 3], ![4, 2, 0, 5, 1, 3]], proof := .tail 114 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4629)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 3, 6, 5, 2, 4], ![0, 3, 6, 5, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 6, 0, 1, 3], ![4, 2, 5, 0, 1, 3]], proof := .tail 71 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4630)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 3, 6, 5, 2, 4], ![0, 3, 6, 5, 2, 4], ![3, 6, 5, 0, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 0, 1, 3], ![4, 5, 2, 0, 1, 3]], proof := .tail 226 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4631)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 3, 6, 5, 2, 4], ![0, 3, 6, 5, 2, 4], ![3, 6, 5, 0, 1, 4], ![2, 0, 1, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 0, 1, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 31 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4632)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 3, 5, 6, 2, 4], ![0, 6, 3, 5, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 0, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 6, 1, 3], ![4, 2, 0, 5, 3, 1]], proof := .tail 13 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4633)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 3, 6, 5, 2, 4], ![0, 6, 3, 5, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 0, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 6, 0, 1, 3], ![4, 2, 5, 0, 3, 1]], proof := .tail 13 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4634)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 3, 6, 5, 2, 4], ![0, 6, 3, 5, 2, 4], ![3, 6, 5, 0, 1, 4], ![2, 0, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 0, 1, 3], ![4, 5, 2, 0, 3, 1]], proof := .tail 226 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4635)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 3, 6, 5, 2, 4], ![0, 6, 3, 5, 2, 4], ![3, 6, 5, 0, 1, 4], ![2, 0, 6, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 0, 1, 3], ![5, 4, 2, 0, 3, 1]], proof := .tail 31 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4636)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 6, 3, 5, 2, 4], ![0, 6, 3, 5, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 6, 0, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 6, 0, 1, 3], ![4, 2, 5, 3, 0, 1]], proof := .tail 155 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4637)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 6, 3, 5, 2, 4], ![0, 6, 3, 5, 2, 4], ![3, 6, 5, 0, 1, 4], ![2, 6, 0, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 0, 1, 3], ![4, 5, 2, 3, 0, 1]], proof := .tail 226 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4638)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 6, 3, 5, 2, 4], ![0, 6, 3, 5, 2, 4], ![3, 6, 5, 0, 1, 4], ![2, 6, 0, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 0, 1, 3], ![5, 4, 2, 3, 0, 1]], proof := .tail 31 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4639)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 6, 3, 5, 2, 4], ![0, 6, 3, 5, 2, 4], ![6, 3, 5, 0, 1, 4], ![6, 2, 0, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 0, 1, 3], ![4, 5, 3, 2, 0, 1]], proof := .tail 125 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4640)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 6, 3, 5, 2, 4], ![0, 6, 3, 5, 2, 4], ![6, 3, 5, 0, 1, 4], ![6, 2, 0, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 0, 1, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 264 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4641)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 5, 3, 2, 4, 6], ![3, 5, 0, 1, 4, 6], ![2, 0, 5, 1, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 2, 0, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 121 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4642)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 5, 3, 2, 4, 6], ![3, 5, 0, 1, 4, 6], ![2, 0, 5, 1, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 2, 0, 3, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 187 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4643)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 5, 3, 2, 4, 6], ![3, 5, 0, 1, 6, 4], ![2, 0, 5, 1, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 2, 0, 3, 1, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 261 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4644)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 5, 3, 2, 6, 4], ![3, 5, 0, 1, 6, 4], ![2, 0, 5, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 0, 3, 1, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 182 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4645)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 5, 3, 6, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 5, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 0, 3, 1, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 8 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4646)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 5, 6, 3, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 5, 6, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 0, 3, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 16 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4647)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 6, 5, 3, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 5, 6, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 0, 3, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 33 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4648)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 6, 5, 3, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 6, 5, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 0, 6, 3, 1], ![0, 4, 2, 5, 3, 1]], proof := .tail 47 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4649)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 3, 5, 2, 6, 4], ![0, 5, 3, 2, 6, 4], ![3, 5, 0, 1, 6, 4], ![2, 0, 5, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 3, 1, 6], ![4, 0, 1, 2, 3, 5]], proof := .low (![3, 227, 140, 75, 127, 133, 30, 188, 160, 128, 236, 162, 63, 165, 235, 236, 51, 101, 86, 134, 165, 165, 194, 10, 7, 58, 211, 66]) }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4650)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 3, 5, 2, 6, 4], ![0, 5, 3, 6, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 5, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 3, 1, 6], ![4, 0, 2, 1, 3, 5]], proof := .tail 8 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4651)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 3, 5, 2, 6, 4], ![0, 5, 6, 3, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 5, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 3, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 16 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4652)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 3, 5, 2, 6, 4], ![0, 6, 5, 3, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 5, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 3, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 33 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4653)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 3, 5, 2, 6, 4], ![0, 6, 5, 3, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 6, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 6, 3, 1], ![4, 0, 2, 5, 3, 1]], proof := .tail 47 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4654)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 3, 5, 6, 2, 4], ![0, 5, 3, 6, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 0, 5, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 3, 1, 6], ![4, 2, 0, 1, 3, 5]], proof := .low (![45, 57, 140, 0, 107, 151, 150, 139, 205, 55, 201, 29, 63, 165, 73, 238, 6, 5, 189, 199, 165, 165, 243, 27, 215, 91, 14, 137]) }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4655)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 3, 5, 6, 2, 4], ![0, 5, 6, 3, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 0, 5, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 3, 1, 6], ![4, 2, 0, 3, 1, 5]], proof := .low (![186, 57, 90, 77, 113, 193, 23, 139, 209, 253, 92, 20, 63, 60, 40, 92, 20, 219, 192, 92, 210, 130, 92, 42, 110, 258, 172, 147]) }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4656)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 3, 5, 6, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 0, 5, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 3, 6, 1], ![4, 2, 0, 3, 5, 1]], proof := .tail 114 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4657)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 3, 5, 6, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 0, 6, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 6, 3, 1], ![4, 2, 0, 5, 3, 1]], proof := .tail 47 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4658)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 3, 6, 5, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 0, 6, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 6, 0, 3, 1], ![4, 2, 5, 0, 3, 1]], proof := .tail 47 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4659)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 3, 6, 5, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 6, 5, 0, 1, 4], ![2, 0, 6, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 0, 3, 1], ![4, 5, 2, 0, 3, 1]], proof := .tail 262 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4660)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 3, 6, 5, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 6, 5, 0, 1, 4], ![2, 0, 6, 5, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 0, 3, 1], ![5, 4, 2, 0, 3, 1]], proof := .tail 228 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4661)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 6, 3, 5, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 6, 0, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 6, 0, 3, 1], ![4, 2, 5, 3, 0, 1]], proof := .tail 218 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4662)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 6, 3, 5, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 6, 5, 0, 1, 4], ![2, 6, 0, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 0, 3, 1], ![4, 5, 2, 3, 0, 1]], proof := .tail 124 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4663)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 6, 3, 5, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 6, 5, 0, 1, 4], ![2, 6, 0, 5, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 0, 3, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 177 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4664)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 6, 3, 5, 2, 4], ![0, 6, 5, 3, 2, 4], ![6, 3, 5, 0, 1, 4], ![6, 2, 0, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 0, 3, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 146 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4665)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 6, 3, 5, 2, 4], ![0, 6, 5, 3, 2, 4], ![6, 3, 5, 0, 1, 4], ![6, 2, 0, 5, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 0, 3, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 112 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4666)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 3, 2, 4, 6], ![3, 5, 0, 1, 4, 6], ![2, 5, 0, 1, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 2, 3, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 161 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4667)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 3, 2, 4, 6], ![3, 5, 0, 1, 4, 6], ![2, 5, 0, 1, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 2, 3, 0, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 187 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4668)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 3, 2, 4, 6], ![3, 5, 0, 1, 6, 4], ![2, 5, 0, 1, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 2, 3, 0, 1, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 175 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4669)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 3, 2, 6, 4], ![3, 5, 0, 1, 6, 4], ![2, 5, 0, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 3, 0, 1, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 109 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4670)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 3, 6, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 5, 0, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 3, 0, 1, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 85 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4671)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 6, 3, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 5, 0, 6, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 3, 0, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 255 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4672)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 6, 5, 3, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 5, 0, 6, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 3, 0, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 102 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4673)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 5, 3, 2, 6, 4], ![0, 5, 3, 2, 6, 4], ![3, 5, 0, 1, 6, 4], ![2, 5, 0, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 0, 1, 6], ![4, 0, 1, 2, 3, 5]], proof := .low (![131, 227, 198, 75, 127, 11, 251, 188, 160, 128, 212, 185, 63, 165, 235, 236, 51, 123, 86, 214, 165, 165, 194, 97, 41, 118, 22, 179]) }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4674)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 5, 3, 2, 6, 4], ![0, 5, 3, 6, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 5, 0, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 0, 1, 6], ![4, 0, 2, 1, 3, 5]], proof := .tail 85 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4675)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 5, 3, 2, 6, 4], ![0, 5, 6, 3, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 5, 0, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 0, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 255 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4676)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 5, 3, 2, 6, 4], ![0, 6, 5, 3, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 5, 0, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 0, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 102 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4677)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 5, 3, 6, 2, 4], ![0, 5, 3, 6, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 5, 0, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 0, 1, 6], ![4, 2, 0, 1, 3, 5]], proof := .low (![247, 57, 154, 0, 168, 151, 132, 139, 205, 55, 201, 138, 63, 165, 208, 238, 232, 169, 208, 99, 165, 94, 119, 81, 159, 153, 61, 116]) }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4678)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 5, 3, 6, 2, 4], ![0, 5, 6, 3, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 5, 0, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 0, 1, 6], ![4, 2, 0, 3, 1, 5]], proof := .tail 255 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4679)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 5, 3, 6, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 5, 0, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 0, 6, 1], ![4, 2, 0, 3, 5, 1]], proof := .tail 102 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4680)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 5, 6, 3, 2, 4], ![0, 5, 6, 3, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 5, 6, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 0, 1, 6], ![4, 2, 3, 0, 1, 5]], proof := .low (![21, 57, 90, 93, 113, 193, 164, 139, 209, 256, 54, 138, 63, 60, 19, 92, 20, 56, 15, 92, 35, 246, 92, 241, 26, 258, 96, 156]) }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4681)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 5, 6, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 5, 6, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 0, 6, 1], ![4, 2, 3, 0, 5, 1]], proof := .tail 114 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4682)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 5, 6, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 6, 0, 1], ![4, 2, 3, 5, 0, 1]], proof := .tail 71 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4683)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 6, 5, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 6, 3, 0, 1], ![4, 2, 5, 3, 0, 1]], proof := .tail 223 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4684)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 6, 5, 0, 1, 4], ![2, 6, 5, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 3, 0, 1], ![4, 5, 2, 3, 0, 1]], proof := .tail 65 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4685)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 6, 5, 0, 1, 4], ![2, 6, 5, 0, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 3, 0, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 248 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4686)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![6, 3, 5, 0, 1, 4], ![6, 2, 5, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 3, 0, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 197 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4687)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![6, 3, 5, 0, 1, 4], ![6, 2, 5, 0, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 3, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 82 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4688)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 3, 2, 4, 6], ![5, 3, 0, 1, 4, 6], ![5, 2, 0, 1, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 3, 2, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 259 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4689)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 3, 2, 4, 6], ![5, 3, 0, 1, 4, 6], ![5, 2, 0, 1, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 3, 2, 0, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 231 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4690)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 3, 2, 4, 6], ![5, 3, 0, 1, 6, 4], ![5, 2, 0, 1, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 3, 2, 0, 1, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 68 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4691)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 3, 2, 6, 4], ![5, 3, 0, 1, 6, 4], ![5, 2, 0, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 2, 0, 1, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 70 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4692)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 3, 6, 2, 4], ![5, 3, 0, 6, 1, 4], ![5, 2, 0, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 2, 0, 1, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 115 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4693)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 6, 3, 2, 4], ![5, 3, 0, 6, 1, 4], ![5, 2, 0, 6, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 2, 0, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 129 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4694)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 6, 5, 3, 2, 4], ![5, 3, 0, 6, 1, 4], ![5, 2, 0, 6, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 2, 0, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 240 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4695)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 5, 3, 2, 6, 4], ![0, 5, 3, 2, 6, 4], ![5, 3, 0, 1, 6, 4], ![5, 2, 0, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 0, 1, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 148 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4696)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 5, 3, 2, 6, 4], ![0, 5, 3, 6, 2, 4], ![5, 3, 0, 6, 1, 4], ![5, 2, 0, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 0, 1, 6], ![4, 0, 2, 1, 3, 5]], proof := .tail 115 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4697)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 5, 3, 2, 6, 4], ![0, 5, 6, 3, 2, 4], ![5, 3, 0, 6, 1, 4], ![5, 2, 0, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 0, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 129 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4698)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 5, 3, 2, 6, 4], ![0, 6, 5, 3, 2, 4], ![5, 3, 0, 6, 1, 4], ![5, 2, 0, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 0, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 240 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4699)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 5, 3, 6, 2, 4], ![0, 5, 3, 6, 2, 4], ![5, 3, 6, 0, 1, 4], ![5, 2, 0, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 0, 1, 6], ![4, 2, 0, 1, 3, 5]], proof := .tail 34 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4700)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 5, 3, 6, 2, 4], ![0, 5, 6, 3, 2, 4], ![5, 3, 6, 0, 1, 4], ![5, 2, 0, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 0, 1, 6], ![4, 2, 0, 3, 1, 5]], proof := .tail 64 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4701)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 5, 3, 6, 2, 4], ![0, 6, 5, 3, 2, 4], ![5, 3, 6, 0, 1, 4], ![5, 2, 0, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 0, 6, 1], ![4, 2, 0, 3, 5, 1]], proof := .tail 240 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4702)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 5, 6, 3, 2, 4], ![0, 5, 6, 3, 2, 4], ![5, 3, 6, 0, 1, 4], ![5, 2, 6, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 0, 1, 6], ![4, 2, 3, 0, 1, 5]], proof := .tail 49 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4703)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 5, 6, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![5, 3, 6, 0, 1, 4], ![5, 2, 6, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 0, 6, 1], ![4, 2, 3, 0, 5, 1]], proof := .tail 240 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4704)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![5, 3, 6, 0, 1, 4], ![5, 2, 6, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 6, 0, 1], ![4, 2, 3, 5, 0, 1]], proof := .tail 145 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4705)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 5, 6, 3, 2, 4], ![0, 5, 6, 3, 2, 4], ![5, 6, 3, 0, 1, 4], ![5, 6, 2, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 5]], proof := .tail 202 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4706)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 5, 6, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![5, 6, 3, 0, 1, 4], ![5, 6, 2, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 5, 1]], proof := .tail 114 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4707)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![5, 6, 3, 0, 1, 4], ![5, 6, 2, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 6, 0, 1], ![4, 3, 2, 5, 0, 1]], proof := .tail 71 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4708)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![6, 5, 3, 0, 1, 4], ![5, 6, 2, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 6, 2, 0, 1], ![4, 3, 5, 2, 0, 1]], proof := .tail 226 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4709)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![6, 5, 3, 0, 1, 4], ![6, 5, 2, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 3, 2, 0, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 260 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4710)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![6, 5, 3, 0, 1, 4], ![6, 5, 2, 0, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 3, 2, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 141 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4711)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 4, 2, 5, 6], ![3, 0, 4, 1, 5, 6], ![2, 0, 1, 4, 5, 6], ![0, 2, 1, 3, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 105 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4712)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 4, 2, 5, 6], ![3, 0, 4, 1, 5, 6], ![2, 0, 1, 4, 5, 6], ![0, 2, 1, 3, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 173 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4713)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 4, 2, 5, 6], ![3, 0, 4, 1, 5, 6], ![2, 0, 1, 4, 6, 5], ![0, 2, 1, 3, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 67 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4714)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 4, 2, 5, 6], ![3, 0, 4, 1, 6, 5], ![2, 0, 1, 4, 6, 5], ![0, 2, 1, 3, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 196 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4715)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 4, 2, 6, 5], ![3, 0, 4, 1, 6, 5], ![2, 0, 1, 4, 6, 5], ![0, 2, 1, 3, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .tail 74 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4716)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 4, 2, 5, 6], ![3, 0, 4, 1, 5, 6], ![2, 0, 1, 6, 4, 5], ![0, 2, 1, 6, 3, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 4, 3]], proof := .tail 135 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4717)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 4, 2, 5, 6], ![3, 0, 4, 1, 6, 5], ![2, 0, 1, 6, 4, 5], ![0, 2, 1, 6, 3, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 4, 3]], proof := .tail 120 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4718)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 4, 2, 6, 5], ![3, 0, 4, 1, 6, 5], ![2, 0, 1, 6, 4, 5], ![0, 2, 1, 6, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 4, 3]], proof := .tail 24 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4719)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 4, 6, 2, 5], ![3, 0, 4, 6, 1, 5], ![2, 0, 1, 4, 6, 5], ![0, 2, 1, 3, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 18 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4720)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 4, 6, 2, 5], ![3, 0, 4, 6, 1, 5], ![2, 0, 1, 6, 4, 5], ![0, 2, 1, 6, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 1, 4, 3]], proof := .tail 257 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4721)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 6, 4, 2, 5], ![3, 0, 4, 6, 1, 5], ![2, 0, 1, 6, 4, 5], ![0, 2, 6, 1, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 4, 1, 3]], proof := .tail 242 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4722)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 6, 4, 2, 5], ![3, 0, 6, 4, 1, 5], ![2, 0, 1, 6, 4, 5], ![0, 6, 2, 1, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 2, 1, 3]], proof := .tail 207 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4723)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 3, 4, 2, 5], ![3, 0, 4, 6, 1, 5], ![2, 0, 6, 1, 4, 5], ![0, 2, 6, 1, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 4, 3, 1]], proof := .tail 84 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4724)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 3, 4, 2, 5], ![3, 0, 6, 4, 1, 5], ![2, 0, 6, 1, 4, 5], ![0, 6, 2, 1, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 2, 3, 1]], proof := .tail 207 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4725)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 4, 2, 6, 5], ![3, 0, 4, 1, 6, 5], ![2, 0, 1, 4, 6, 5], ![0, 2, 1, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 74 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4726)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 4, 2, 6, 5], ![3, 0, 4, 1, 6, 5], ![2, 0, 1, 6, 4, 5], ![0, 2, 1, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 4, 3]], proof := .tail 24 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4727)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 4, 6, 2, 5], ![3, 0, 4, 6, 1, 5], ![2, 0, 1, 4, 6, 5], ![0, 2, 1, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .tail 18 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4728)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 4, 6, 2, 5], ![3, 0, 4, 6, 1, 5], ![2, 0, 1, 6, 4, 5], ![0, 2, 1, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 1, 4, 3]], proof := .tail 257 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4729)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 6, 4, 2, 5], ![3, 0, 4, 6, 1, 5], ![2, 0, 1, 6, 4, 5], ![0, 2, 6, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 4, 1, 3]], proof := .tail 242 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4730)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 6, 4, 2, 5], ![3, 0, 6, 4, 1, 5], ![2, 0, 1, 6, 4, 5], ![0, 6, 2, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 2, 1, 3]], proof := .tail 183 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4731)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 6, 3, 4, 2, 5], ![3, 0, 4, 6, 1, 5], ![2, 0, 6, 1, 4, 5], ![0, 2, 6, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 4, 3, 1]], proof := .tail 84 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4732)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 6, 3, 4, 2, 5], ![3, 0, 6, 4, 1, 5], ![2, 0, 6, 1, 4, 5], ![0, 6, 2, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 2, 3, 1]], proof := .tail 183 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4733)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 3, 6, 4, 2, 5], ![3, 0, 6, 4, 1, 5], ![2, 0, 1, 6, 4, 5], ![6, 0, 2, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 0, 2, 1, 3]], proof := .tail 39 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4734)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 6, 3, 4, 2, 5], ![3, 0, 6, 4, 1, 5], ![2, 0, 6, 1, 4, 5], ![6, 0, 2, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 0, 2, 3, 1]], proof := .tail 252 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4735)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (4608 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 4608 ≤ id.val) (hhigh : id.val < 4736) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 4608)) = true := by
  let j : Fin 128 := ⟨id.val - 4608, by omega⟩
  have hsum : 4608 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (4608 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard036
