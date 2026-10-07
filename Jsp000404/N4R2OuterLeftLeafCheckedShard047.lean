import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard047
open N4R2OuterLeftReplay

-- Cycle fingerprint 00521f72536de6fae549ba98f60c026256a1dc5370d49df5dae1f46852ffbffd.
def localCycle00000 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint 0088bea689d5ad9e56fcba5aaaec0caaa842b5fc531b3bf41f7c2d713d1017fa.
def localCycle00001 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 6]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 23 2, .gapLower 1 4, .triangle 20 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0]

-- Cycle fingerprint 014c56d3b555edbde55b66bc4984269eb19a79607b775c8f834e4e84a306d9ff.
def localCycle00002 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-3, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint 0223a589ad70eeb04e9378e98b1dc8e546101d29d639a55d107a9eee2e053feb.
def localCycle00003 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 027665354baa0ab1defc842fe127692def5dc1642a617153facf01dec58bd87d.
def localCycle00004 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6]
    constant := ![-3, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 22 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 18 2]

-- Cycle fingerprint 034203772c447a0753e7ec3a25be553dc1fb26ab60632806d729095e196ea304.
def localCycle00005 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 03439e5b6b25f7ef062c272fbd2fc2a8932fce76f76bc8863cc5136af8e4b8f6.
def localCycle00006 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4]
    constant := ![0, -1, 3, 0, -2, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .triangle 2 2, .triangle 12 0, .triangle 28 0]

-- Cycle fingerprint 0467d939bf984775377347fc8e9e34bab33b9fe01012553ae2f2015eb04e7242.
def localCycle00007 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 23 1, .triangle 22 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 06b572684cb15a308b881cfc5e74597a36de6801b2037df689e8a4805715009c.
def localCycle00008 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, 0, 3, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint 080374ffeefb80f3401e3cd6e14487afb5c39250925176e8eda218bbb626a463.
def localCycle00009 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 6]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 6 3, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0]

-- Cycle fingerprint 0803af0393cc53c31ef75820eacb771d1666d5ae830e6429bbc304ee4302e24e.
def localCycle00010 : Cycle where
  length := 15
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 0 2]
    constant := ![-1, -1, 0, -1, 3, 0, -1, -1, 0, -2, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 0 2]

-- Cycle fingerprint 084ecb729763235ee8b12561f0dbb171cede355f75dfa5661607578dd8c79188.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 0967416f52e5486571f82f052ae04ddb4e294cdeb1e89ffc6de46f5c4dca58d2.
def localCycle00012 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 0ac5f0d6de3d8f21238d7bfb963b1620921243004d2e11d63dc611c7fbc716fe.
def localCycle00013 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 2 2, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 0bce2bcc64e1ef4e1fb26ea14f8e0fdddb3a1c1d78eb26bd4fbd80c827094042.
def localCycle00014 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 2]
    constant := ![3, -2, 0, 0, 0, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2]

-- Cycle fingerprint 0d3df9f8f43f6d381c9c448a3335d10ace72209edeb21eeb51e9b4d1842a7b80.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 20 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint 0d97ef15a963b078912bfe8fc8c65409cb675baab71c6dd58990842fe31984d7.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 18 2, .gapLower 1 4, .triangle 2 2, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 0dfc225889118c52fb50736185be743b36a526d036d18e6c413c898cbcf51a1b.
def localCycle00017 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 5, .distance 5 6]
    constant := ![-1, 0, -1, 3, -2, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 3 2, .triangle 14 0]

-- Cycle fingerprint 0e48e8b36b4a52db7bedd9da68b976a0712eabcf9f11194fc7603eb673b98054.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 22 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0]

-- Cycle fingerprint 0e4b208e22682e3ecd6fdbd0d71aa9b909348662cabeb0c196cfee191cdeb47d.
def localCycle00019 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, -2, 0, -2, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 22 2, .gapLower 1 3, .triangle 4 2, .triangle 14 1, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 0e546a8dfd4303894170b4c521a45de2c7986aa9814f243529d56a5939a496a8.
def localCycle00020 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 0eb5f16c3294ede1b5210b24d702cd9ca9e6829c4199001d46b9376ad160e346.
def localCycle00021 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 24 2, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint 100910675274ba5afd7270e3fa8b5e14f3b3920f1b798c6e74c9315af2eb85e4.
def localCycle00022 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 34 0, .triangle 30 0, .triangle 26 1, .corridorLower 2 3]

-- Cycle fingerprint 10708729dff040ca1acf1305720b075e0f131f0a958c667a2ff554a16352a34c.
def localCycle00023 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 4, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 2 2, .triangle 6 1, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 1099f83c0f422cc603c94423b867b6f2432bbe21ebf28b74d151ee9e25e9d15a.
def localCycle00024 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![-1, 0, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 22 2, .gapLower 1 3, .triangle 24 1]

-- Cycle fingerprint 126d021c1ccc57d7ac304f58ae5ee28955c90661aadbd1837d83fbf8524545c9.
def localCycle00025 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5]
    constant := ![0, -1, 3, 0, -3, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .triangle 4 2, .triangle 14 1, .triangle 30 0]

-- Cycle fingerprint 135f0f78678bcf4300f34ac31c3ab5e5de921e377bfc5076cf949fdcbf111142.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5]
    constant := ![-1, 0, -1, 3, -3, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 4 2, .triangle 13 1, .triangle 12 0]

-- Cycle fingerprint 13617db116de09efdfcbe4e6572bb50a9ffb21b5a108586c4aba5c898f92a233.
def localCycle00027 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint 14e0779e585e7e4458c548d7b1e995d3f88f2cf64e09195b8b9eb5cc406537fa.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 4 5, .distance 2 4]
    constant := ![0, -1, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 22 1, .triangle 28 0]

-- Cycle fingerprint 153929c7c45ae76c5e7bfb39bdeddf3e991c446cc76eb9dc80d2117dc6aa947e.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 1546a9a38150f9a763cda117ff804c922898917a226ba06532d6037d68eb6bb6.
def localCycle00030 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .gapLower 4 0]

-- Cycle fingerprint 1568c0bbe418ec31c7972cdda6504fcbc8d82693417fea7a2d0dc1d5103e93a5.
def localCycle00031 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 4]
    constant := ![-3, 0, 2, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 20 1, .gapUpper 3 3, .gapUpper 5 5, .gapLower 6 5, .triangle 32 0, .triangle 19 2]

-- Cycle fingerprint 159678bdfdb91b51ad056146ef0da2f6b693ccc2f024aec83dce3020ac2790fd.
def localCycle00032 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 166dd60398c05838e361c63cad17a12cc2417d12da1f7243af4185b3f45b9133.
def localCycle00033 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 22 2, .triangle 24 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 17bebf85f958c78a7b0131a5cdd4825296b446ebb9ef947968a3d835e1dfc8e4.
def localCycle00034 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, -1, 0, -1, -3, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 2 0, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint 188d97385e8470f330136a7cdb6a540a33b2188c24f29c30d98e9be285d7f1f0.
def localCycle00035 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .gapLower 6 3, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 18b0baeeb6749f12b17ddab2d3dc3c66eeb599aeb2fb815bd8b8b45365b5fff8.
def localCycle00036 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 29 0, .gapLower 4 0]

-- Cycle fingerprint 1da8b2152a84945af0201828a60fa6b8ce6a01ddd94292a2b5fb9b3337370449.
def localCycle00037 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 1 6]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 18 2]

-- Cycle fingerprint 1eb62a2f137d7aac8c59986ce089137f2b80b59fbe0b41d4b3ef29eec276d691.
def localCycle00038 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 0, .triangle 28 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 1fbe7eecb892757dc8632ac757ba52f41b2fc48862fd1633252ecc33fb54d57b.
def localCycle00039 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 2]

-- Cycle fingerprint 2083fe65eefe9d507d5d347c88a6bab23286cd1553b3c9ea84120318d2731b64.
def localCycle00040 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5]
    constant := ![-1, 0, -1, 3, -2, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 2 2, .triangle 12 0]

-- Cycle fingerprint 213ac813c76d2e30b78d3a1d9a2aea56565673b0d36783e8a32eb86cf2201570.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 5]
    constant := ![0, -1, 3, 0, -3, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 3 2, .triangle 14 0, .triangle 30 0]

-- Cycle fingerprint 226c799c4be604eeb184814466e9d16d4f399b9fd71325779fb9888ca5c8435a.
def localCycle00042 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4]
    constant := ![-1, -2, -2, 0, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0]

-- Cycle fingerprint 24ba3179a9053286c661b3b2af700606300372f9dedd7d8de48e8b70d1ac4eea.
def localCycle00043 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 4, .gapLower 1 3, .triangle 24 1]

-- Cycle fingerprint 25d297b41684e114a4ad5bc24d8cca501bb328dcd3b291b71017ea180519e679.
def localCycle00044 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 3, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint 26d004cbd8c590c6525b9c3d931ea397b826bcd8fed29cdf5918fef4fc57e462.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2]
    constant := ![3, -2, 0, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2]

-- Cycle fingerprint 27b82362f5cd5dbd5c8e4c0a7c0edf3d082c02c0ba7bf2cfb5180c3e82ba35ba.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 22 2, .gapLower 1 4, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0]

-- Cycle fingerprint 283d90515d443e794850ef64287bd2a43a08a4dabd5dce47cfee015abd6f8de4.
def localCycle00047 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![-1, 0, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 2, .gapLower 1 4, .triangle 22 1]

-- Cycle fingerprint 284aa27702373b93b9ab3518a0daf6dcec93f09a539e44ee51e82cdb5a0e8f15.
def localCycle00048 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -2, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 3, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 2a977c96141908bf3990635620d25be5248d8d787cbad3e94451af5012c0c6e5.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 2aa30f93523b5c5c4ab49f725fd1abc2c274eede440d9753e2c5a96557fc3e20.
def localCycle00050 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, -1, 0, 0, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 2dc767f5cebd8cca45ea42256b03ba907fb2fda095f32a62952a50ba558d53b3.
def localCycle00051 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 2e0e8c8d38814d1a0d11fd33863a0b53a9edbc0a76868f3e02fd56fcfb87587a.
def localCycle00052 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 3, .gapLower 1 4, .gapUpper 5 3]

-- Cycle fingerprint 2eca5049cf8cfb0bacc356a48d4ddaa25857c7225fb373eb4cd397ce4726116c.
def localCycle00053 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, 0, -1, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 16 2, .gapLower 1 4, .triangle 24 1, .triangle 20 1, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 2eeb717854d5534f136cafd416abc919a61db05b565fc8290a620ce26497f572.
def localCycle00054 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 2f1124a54bf45740fbeea5cac3addeefc3ea21d5c9d18f7aa99bd89b7645a019.
def localCycle00055 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 2f82cae4b082b1cb3b8fd7f3db357a2c2b6f68259e52cbe16ac75d19e9065a03.
def localCycle00056 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6]
    constant := ![0, -3, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 21 2, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2]

-- Cycle fingerprint 2fb2fd1a7823a1a31ea79d941af5a5c4f133d776e33999c5e67c0528f91eb18e.
def localCycle00057 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .theta 6, .theta 5, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 6]
    constant := ![-2, 0, 0, 3, -1, -1, 0]
    coefficient := ![-1, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true] }
  origin := ![.gapUpper 6 6, .thetaNext 5, .thetaNext 4, .corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 2]

-- Cycle fingerprint 2fcfcc87cce986f59eed78d4e7032540685e1645c590bff0bfba401fb907cbfc.
def localCycle00058 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 301a095724cb3e47d6331eba71e91effe748847a4c93461df636303129097dd9.
def localCycle00059 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 3, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 0, .triangle 21 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 318e28414aa86463ad2376e8d9f33179672f641f86332ce3f5ea781671067c36.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -2, -2, 0, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, false, false, false, false] }
  origin := ![.triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 4 2, .triangle 13 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 31afcce418d1790cf041e73d0758df8a48baab77f338952f885a9c6a775bb2f4.
def localCycle00061 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, -2, 0, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, true, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .triangle 22 1, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 323ade28f8caf9f55625036b6468a09d417d880a396facf5892ff0741d400341.
def localCycle00062 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 3263f66f60639555d7f7ccbee43f3c822eb57899d7d919c1ace12dfaa927d81d.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 32e15e3230745da6cba2915ab6971351fc19ca4d8a7c526f04c547ccba36e8c4.
def localCycle00064 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 32e97fd15019c96edd440cca592e1d318f189b31ef9a3ec115c9b6a727cae9e1.
def localCycle00065 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 3334f61181f84ca6e4c6036b1604aaa2f5ab8990871257e273d695b2c33754d9.
def localCycle00066 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .triangle 28 0, .gapLower 4 0]

-- Cycle fingerprint 339ac03128f14ebb315257c126af64ebed24245738cacf85765391d73800bcf3.
def localCycle00067 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .theta 0]
    constant := ![0, 0, 3, -1, 0, -1, 0, -1, -3, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint 340562d7a4ff97204092f3e43448b8760f4c7d560c2be2ace9606df5ec90fc0c.
def localCycle00068 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6]
    constant := ![-1, -3, -1, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint 344ce9af0544d00210fc6cb393cfefda191fe43282996569817458147c8610e3.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3]
    constant := ![-1, -3, 0, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 0]

-- Cycle fingerprint 357eb6b0d6e9cce2cffc9f50600c3aca24692be7f113dea576f88fce9d659a57.
def localCycle00070 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 1 5]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 6 5, .triangle 24 0]

-- Cycle fingerprint 35cd8013b6b47dcd8aa6549186ac32b97761dda7470018b5cc1164a65dc273d0.
def localCycle00071 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 16 2, .gapLower 1 4, .triangle 3 2, .triangle 12 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 36639f445fded3b09424fb9d1ca79709057ab5019a0270f66959ed815908b905.
def localCycle00072 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 21 2, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint 37c35bfde908ef279b63142a8f9479107508f863fdc43563df2cc417b909fd87.
def localCycle00073 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, -2, 0, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .triangle 22 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 37dffbfe6c32585a6a48a6a55ce885c032069e4631a00920600c35ca5298ce4d.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 4, .distance 0 4, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2]
    constant := ![0, -3, 0, 0, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, true, true, false] }
  origin := ![.triangle 18 2, .gapLower 1 4, .triangle 2 2, .triangle 6 1, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .corridorUpper 1 2]

-- Cycle fingerprint 386e5afce63ef933e094915222ce1b561892b8d4cf1dfd11da5cbf69b436c56a.
def localCycle00075 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -2, -2, 0, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, false, false, false, false] }
  origin := ![.triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 2, .triangle 12 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 3a1b0de3c2d416afbde575b96e85054e929dcc86009a118a354b8e68843d7325.
def localCycle00076 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .theta 1]
    constant := ![2, -2, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .thetaNext 1]

-- Cycle fingerprint 3c1a9bae1abced6725cf0f2c2fcb11a4ac1b1debe63231a0da58603ead699ec2.
def localCycle00077 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 24 2, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint 3c350f4c85fc54061bbcafc6a895face97a52e31fae4a5154734722428b3fd01.
def localCycle00078 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-3, -1, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 23 0, .triangle 34 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 3cd7b3f75f820c82296e9148bee0c6437f28de6f0e1fd00010d54e44dc089b10.
def localCycle00079 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 34 0, .triangle 30 0, .triangle 28 1, .corridorLower 2 4]

-- Cycle fingerprint 3d13fafae88973048d0c3b27323b79cbe3e05e69222d1769ebb95ebc21e5f6f0.
def localCycle00080 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![-1, -2, 0, 0, 3, -1, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .gapLower 5 3, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint 3d3b7be79afaacfa2e5d2f1d62911cfd9b4aa46a04bb8439efb8fcca8d274fa0.
def localCycle00081 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6]
    constant := ![-1, -2, -2, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2]

-- Cycle fingerprint 3d7d70b293254cadfe8d7794cf6a4da1913da925b21ea56561888ed4c6e67776.
def localCycle00082 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, -1, 3, -3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 2 2, .triangle 13 0, .triangle 34 1]

-- Cycle fingerprint 3e58997d907a230ff5c5233458f3ec0921a159a15ffcb85269cb06c6479415d2.
def localCycle00083 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, -1, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 23 0, .triangle 34 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 3e9c69ae50add6f82aa5a8c56a3860d291ee31bc09022a518707a4a0762bada4.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 6, .distance 4 6]
    constant := ![-1, 0, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 2, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 40104c85c1d689c63ae3289306bd9cae4d93fb9c7cbfd9838bf3cab434157b88.
def localCycle00085 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 4084a1e816d0224e6f03c47276fbd6b63480446daea05288553a1188620f60e4.
def localCycle00086 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![0, -3, 0, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false, false, true] }
  origin := ![.triangle 22 2, .gapLower 1 3, .triangle 4 2, .triangle 14 1, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint 4103cc0515aa47df78e5d1b0bb5dff52cb64a2250ee9d801ccaad4f16436c626.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, 0, -1, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true, false, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 429d7a09dcda6c0c0c97182b6054bf00b927483c8919d3976324ea8964c488db.
def localCycle00088 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-3, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 24 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint 43f2ab8285abcf4a8cd51a963d29d4194684ef2849cc1a5b637e6b4a26dcf757.
def localCycle00089 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6]
    constant := ![-1, 0, -1, 0, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 2, .triangle 22 2, .triangle 24 0]

-- Cycle fingerprint 443563070970df43959f2e926746a3c9f5f722341af3b2bf27803e37e676bd41.
def localCycle00090 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 449efaa1be83dae35ba9bdf774322e700f68734cbdec8301fadfcc4b842ce26c.
def localCycle00091 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 16 2, .gapLower 1 4, .triangle 3 2, .triangle 14 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 45e9480a447c176066129cd3cfb6d9d3968789004aafaaf09b8be894f9853cf7.
def localCycle00092 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint 464c73cffbadc8453155fbee9630a57185660a489d8544855ebfb748c24ea34b.
def localCycle00093 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 12 2, .triangle 14 0, .triangle 30 0, .gapLower 2 2, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 468946cde2aa73703dbae91e150c5a23580228ce28a8ff35fc84409ee77e65f4.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 33 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 4729f0e2888116c05612179bb2cd1c4de76d5f50e8ed627d47f60d5eaef8540e.
def localCycle00095 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .theta 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 4]
    constant := ![0, 3, -1, 0, -3, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.gapLower 4 0, .corridorUpper 3 4, .triangle 31 0, .triangle 22 2, .gapLower 1 4, .triangle 4 2, .triangle 8 1, .triangle 29 1]

-- Cycle fingerprint 479a2a4240b54ba514f6e1f1832ba681a94e3b068cd9449c7f6ad2f536271a29.
def localCycle00096 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0]

-- Cycle fingerprint 47aeecc03227f981ac1b7b98a72538c78998087b1d37a6c2674fd604788b8d32.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, -1, -1, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 49160ab5c446ca2b4e99ad4550c91ecbfd095e85f905b56ac769a69f6b11e60c.
def localCycle00098 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 4 5, .distance 2 4, .distance 2 3]
    constant := ![-1, 3, 0, 0, -3, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .triangle 22 1, .triangle 28 0, .gapLower 2 1]

-- Cycle fingerprint 49f63891cd9e8d7b8864111a0301b20006fcd6fbe9e2a7921dd383d2cd6ad934.
def localCycle00099 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4a18de57828c5ca83d8326ad433360be866d68d3607fdc218b14e86ddb64e795.
def localCycle00100 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 4a8804537d4f7df4499b24f7cb8435da8f8b2a3c5a7ba9682f43858a96d68fac.
def localCycle00101 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5]
    constant := ![-3, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 2]

-- Cycle fingerprint 4b2031fb80a0951111c793c3105ae026fc2e41c966ed6a7cec17878706a73157.
def localCycle00102 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-3, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 22 2, .triangle 24 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 4b4af92bba486f99b50dd895357772b0b6dd4266c5184ca53629c53cfec748dd.
def localCycle00103 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint 4c09ce276b692a142662beef21bb5324c3a9a95cd78e510c3e0292455a53e529.
def localCycle00104 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, -2, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 24 1, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint 4c2e74b029df501eff4cd337d525651f24fbf3f72175f426f93663470d291325.
def localCycle00105 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 5]
    constant := ![0, -1, 3, 0, -2, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 3 2, .triangle 14 0, .triangle 30 0]

-- Cycle fingerprint 4c77d380ff901a863f4b269996d7cd032772d6f889975966775be3fcd2f783f4.
def localCycle00106 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-2, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint 4d3c97b5452523191ddb8cd02ced549ccef4d7fbb68b2ad08212a5ce250474bc.
def localCycle00107 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 1 4]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 5 4, .triangle 22 0]

-- Cycle fingerprint 4d5b39d017b42f6dcf08532014d02b738b4fc7f0a3662bb975c1ca4ee7c51fdf.
def localCycle00108 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 5, .distance 1 6, .theta 1]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 17 2, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint 4d935be8c41fde894e2502febe9f0b7282644debfec6c1dce43c20b12a22d47b.
def localCycle00109 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 24 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 4e2516ce98fa02cf3bad7c45c4415c94d7a49357d21d496dafb0d99f4226b947.
def localCycle00110 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![-1, 0, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 4f5a22a12083c0ba5290b08385964c55814bb1ec38c408c48336494b72285e2b.
def localCycle00111 : Cycle where
  length := 6
  data := {
    node := ![.distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5]
    constant := ![-1, 0, -1, 3, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 22 0]

-- Cycle fingerprint 5018858cdbe62f84a8f18cdf6e9c67c44592ca1cd46987f7d23fb23caf16a72b.
def localCycle00112 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 6, .distance 1 5, .theta 1]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 18 2, .gapLower 1 4, .corridorLower 1 5]

-- Cycle fingerprint 5031e120fefaf5029fd53e2820eaf1f5fb5f6cf80ec7b60adbe53a9b1588cc92.
def localCycle00113 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 24 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 22 2]

-- Cycle fingerprint 503589b2595d7a4b41abb922000f00978af437dc121d7d23d92d20e903795464.
def localCycle00114 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![-1, -2, 0, 0, 3, -1, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint 50a0bb902577cb03e4d29ea5270e3ca2e209887448466d08ff90573481159a54.
def localCycle00115 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-3, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 3 2, .triangle 14 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint 50bcbb4277b5811ca46e7c4faa2c10c61b5ab2646d04457e2bbd7f8f396c9225.
def localCycle00116 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 0 4, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .zero, .theta 1, .distance 1 2, .distance 1 6]
    constant := ![-2, 0, 0, -1, -1, 0, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 2 2, .triangle 6 1, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaLower 3, .thetaUpper 1, .gapLower 1 6, .triangle 18 2]

-- Cycle fingerprint 5428b724fd05f79c5802cff3018a0483521cbf28ab36dbae58b63313a9ed4293.
def localCycle00117 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 22 1, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint 5513bbdbc41802a4f2e1812e7986ea1f3b0a463c9bc655b257d3b7b5c3810577.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 4 5]
    constant := ![-1, 0, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 55934910b99eea73eaeefd5b2ed65129696baa6ff551b09723a6da224e3a9129.
def localCycle00119 : Cycle where
  length := 3
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .theta 2]
    constant := ![0, 1, -2]
    coefficient := ![0, 1, -1]
    strict := ![true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapUpper 2 6]

-- Cycle fingerprint 564ee0d619704debd586c6af03394824f040bace912d92cf04fabb521d7af6b5.
def localCycle00120 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, -2, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 22 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 5805db678bf6328c92a9511dccf3257a296f05357e0cb0c020fe50fb733f69df.
def localCycle00121 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 13 0, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 58a3c266584270148253fb60d2c09fbca6c25a98ae8542d8ebc8ad4eb36cfc8a.
def localCycle00122 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 4]
    constant := ![0, -3, -1, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 0]

-- Cycle fingerprint 59cc5ffa996bc19c7c1b8405cf09c5b98e864303398cff755f410774ad4d0239.
def localCycle00123 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, 0, -1, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 17 2, .gapLower 1 4, .triangle 23 1, .triangle 19 1, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 59e723b71ca801f658cff88b530430996737a22af3f72c6a4e66899e09dc50aa.
def localCycle00124 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1]

-- Cycle fingerprint 5a3af15ed1ce728f122f6ecc278745f76ae0cb7a78cec1f2f4f12fcbca9d0917.
def localCycle00125 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5]
    constant := ![-1, 0, -1, 3, -2, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 4 2, .triangle 13 1, .triangle 12 0]

-- Cycle fingerprint 5afc8390387a33d6ab4640d3dbd713ba6f7e2c03bc6886664835381ac83079f4.
def localCycle00126 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 5bf12a6d8e0bb7411f59d56fbfe1029603b5f02847d29ce269787c3488860c4e.
def localCycle00127 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -2, -2, 0, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, false, false, false, false] }
  origin := ![.triangle 18 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 2, .triangle 12 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 5d73e8accd54f6d861750c9fd4b41a29ee40c7ad007179bf43d1b1904b45757a.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 4, .distance 0 5, .distance 5 6]
    constant := ![-1, 0, -1, 3, -3, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 2 2, .triangle 12 2, .triangle 14 0]

-- Cycle fingerprint 5db77a44c64e8a96c4e5b10df8dffa82e3acdfd24d54859dc49037e1e7c1a38a.
def localCycle00129 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, -2, 0, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 16 2, .triangle 22 2, .gapLower 1 3, .triangle 24 1, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 5e29f29680339a5164dc989c89d8022feaa528ba15801bee92dcc6b4bd323934.
def localCycle00130 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 5f93ab30f7e3049e0fa0d7e19aaace070f871b67125ba77226deb65b4d4f708d.
def localCycle00131 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 31 1, .triangle 19 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 5fabb4db954e057c2c818a74ad9c2d79f550387bb85cbb711a95ea1667893e79.
def localCycle00132 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 5 4, .gapLower 5 3, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint 6039d2fbc95da9c000492cbfc3fbe71c0996e2e843a41cd7f626e95689520651.
def localCycle00133 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .triangle 22 1, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 60d11d484b7e86316bb03406b4c0c82f397f84e0792219a73eb51be901397e49.
def localCycle00134 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 62216832f5f446e87c6a6a4d8d4b7e868c443a5e2febaee993693483dabeae3d.
def localCycle00135 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 1 5]
    constant := ![0, -2, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 19 1, .corridorLower 1 3, .gapLower 1 6, .triangle 17 2]

-- Cycle fingerprint 65de18ae97778e4aeeeefa70ee8ae18c43a4bbd6ff104cc2608c7cb7b18e939f.
def localCycle00136 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint 679ae7fc30a63f67d8e0af9c0bbc912de2c993f0667c815f267bef4101ee7d89.
def localCycle00137 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, -2, 0, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, true, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 16 2, .triangle 22 2, .gapLower 1 3, .triangle 23 1, .triangle 29 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 67a06e6dc44c4fa960134aae6520066de2fa8bb2403fa6f9e41e5f115bde86f8.
def localCycle00138 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6]
    constant := ![-2, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 22 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 18 2]

-- Cycle fingerprint 67f6ca1d506be8766191a709455501ee3ba0002dc8a73aca90d2369f0dd00f67.
def localCycle00139 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .theta 4, .distance 3 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 0 5, .distance 2 5, .distance 2 4]
    constant := ![0, 3, -1, 0, -3, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.gapLower 4 0, .corridorUpper 3 4, .triangle 32 0, .triangle 23 2, .gapLower 1 4, .triangle 3 2, .triangle 7 1, .triangle 28 1]

-- Cycle fingerprint 689004042d9b8a0871a992f039aa3e823abaaf9bbe42ba25669bf7e27a06f3c1.
def localCycle00140 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 2, .triangle 8 0, .triangle 7 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 6936811fef83983b2296f147c91ee55a7c694a50e065b129101d072dc95b0ad6.
def localCycle00141 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -2, -2, 0, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, false, false, false, false] }
  origin := ![.triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 4 2, .triangle 14 1, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 6a6f9e36f568723fc4bf9f6aa4ac4266117635ca0e0cdbaff163ee523aeca34f.
def localCycle00142 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 6]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 6 5, .triangle 24 0, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint 6bfccc1763449542c5aeae2e9f96672be37b52ff1fcd1140e0f2063d33cf4e56.
def localCycle00143 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 3 5, .distance 1 5]
    constant := ![-2, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .gapUpper 3 3, .triangle 20 2]

-- Cycle fingerprint 6c67051834f247c950ebc339abbd79382ecd400f7ded275a60089973dce23757.
def localCycle00144 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1]

-- Cycle fingerprint 6d83ccabe2fc2b444e831be17fa95ef31ce72a091c580abf41e0232afff12732.
def localCycle00145 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 6, .distance 4 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 6e1b383d94287d5767eac12c7d871c953ea5d1029a3a4615f79a9f7577a47f45.
def localCycle00146 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 24 1, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint 6e70b5df5fb9cbf1642187a19f040f27655f8cdf65ba2be974d3dd3ce03c170b.
def localCycle00147 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-3, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 23 1, .triangle 22 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 7299896991a8d60f06e2e584a75bb1c4a4a765e2f01c7cacb6d87fa102668d85.
def localCycle00148 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 2, .triangle 13 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 734f2afc116bfe403b285d7cb2835749bf89437ae2b942329d682b0e0820b0c8.
def localCycle00149 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![0, -3, 0, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false, false, true] }
  origin := ![.triangle 22 2, .gapLower 1 3, .triangle 4 2, .triangle 13 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint 737f5bd8b77a42089cf3da023dd908a07f398dd71d57aa24709cf15cb6f97187.
def localCycle00150 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 12 2, .triangle 14 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4]

-- Cycle fingerprint 73adfa9c72fc3b1e7d29fb8786a9036495614803a55d1d72337210818ad8eb16.
def localCycle00151 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5]
    constant := ![-1, 0, -1, 3, -2, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.triangle 28 0, .triangle 25 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 4 2, .triangle 13 1, .triangle 12 0]

-- Cycle fingerprint 754dd6571ea8b0c39ec878e53f94ab5bd68eab804274160fe4f434e6c90e8106.
def localCycle00152 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4]
    constant := ![0, -2, 0, 0, -1, 0, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false, true, false, true] }
  origin := ![.triangle 22 2, .gapLower 1 3, .triangle 4 2, .triangle 13 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 2]

-- Cycle fingerprint 7594b542407a6a97089b9564244ca0c89e0f517734189ee4472c9b51b42f4e63.
def localCycle00153 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![-2, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 76bf89fcec050ab6e75b78e11864f94dfb4f9c016132a6e9e013baf24d004671.
def localCycle00154 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 17 2, .gapLower 1 4, .triangle 4 2, .triangle 14 1, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4]

-- Cycle fingerprint 76e44a8fbd02ccf3d95a95609e1a463370902baf7ca9cd830791f39bd0a20cc1.
def localCycle00155 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 7750b421a1df08bf47041047ba02cb42d1bf7719672d1a6c7f8b9826bed8b681.
def localCycle00156 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![0, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 22 2, .gapLower 1 3, .triangle 21 1, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint 79a982a8784285275fa17f12e0cf9aa39190bb6fbfaf1cf35acd56d13b8bb113.
def localCycle00157 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 3 2, .triangle 14 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint 79bc0ef238e0985c5eca508aca36ad1d3b763dfdb69ca5fb6f6f4edaad9e5713.
def localCycle00158 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4]
    constant := ![0, -2, 0, 0, -1, 0, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false, true, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 3 2, .triangle 12 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 2]

-- Cycle fingerprint 7a456fda9c02d6c690a576f57d79a89a33114c22b9acc1929cfd565a964c4d0b.
def localCycle00159 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 7ac11edabceb51a6882dceb6d36755c7fc16f99cde664db324ec6a484759bc18.
def localCycle00160 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 4, .distance 1 3, .distance 3 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 3, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint 7b043b4ac611fab3b996889521840abb384fd180d9f7f9008bcc50d6edf279d4.
def localCycle00161 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6]
    constant := ![-1, 0, -1, 0, 2, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 2, .gapLower 1 4, .triangle 24 0]

-- Cycle fingerprint 7b735d61bc88fe7a17f15d5ddd0647d8c690b3e7b0c831f9872d34b40857b700.
def localCycle00162 : Cycle where
  length := 6
  data := {
    node := ![.distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5]
    constant := ![-1, 0, -1, 3, -3, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 22 0]

-- Cycle fingerprint 7d4898512e18310a26b0b395c5d5f7774527a8c88d9e1a459e98796715352a3c.
def localCycle00163 : Cycle where
  length := 6
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 5, .distance 5 6]
    constant := ![-1, 0, -1, 3, -3, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .triangle 24 0]

-- Cycle fingerprint 7d7e1d0dd5386a159baaf94400caa63ea3a1e0ff348a02de9a6c21d6a2999beb.
def localCycle00164 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 0, .triangle 28 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 7d9472a539c8e4f205b0cb542dcf36c1171d3dbd81c2377b2862bea059c3c0c5.
def localCycle00165 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 0 5, .distance 5 6]
    constant := ![-1, 0, -1, 0, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 7 2, .triangle 14 0]

-- Cycle fingerprint 7e8cc7f96c662586d5c0601dae8631f78552471f12e5bb509349d7c9239e5455.
def localCycle00166 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 2, .gapLower 1 2]

-- Cycle fingerprint 7f38846cb8f12d6551120deb0306b6b1124c427b4774ab4dc0fca71338df0519.
def localCycle00167 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint 7f43ef3f1fef2424ba7eaa1b70500360a408de4b4c8b1dff869e4b27b02527d6.
def localCycle00168 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 3, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 7ff689959cc9f7e4d61983bbb042c6aaf3a19c6106b4fcb35b61b7afe5f550b0.
def localCycle00169 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 20 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 823b2f065399c1b549841a28a2a8fa1ccc8df08624a25034b3fe8430df8b41f6.
def localCycle00170 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![0, -3, 0, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 3 2, .triangle 12 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint 82a0ffa3d9333ba70b6cd6625221c083d43f2a139b5423f1bdc46fc776c9c97c.
def localCycle00171 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 82e8359514f6b6e0d0d0ce793bbf7e71e19f8b851c9164be513843de54f8aaf9.
def localCycle00172 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 6, .distance 2 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 6, .distance 0 6]
    constant := ![0, 0, -1, -1, 0, 0, 0, 2, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, true, true, true, false, false, true] }
  origin := ![.triangle 8 1, .triangle 29 1, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 4 2]

-- Cycle fingerprint 833892c1e37e7ba240cd8940f5d14aa770b15fdf38bb77ab27217226699c0607.
def localCycle00173 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![0, -1, -2, 0, 0, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 1, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .gapLower 1 4, .triangle 22 1]

-- Cycle fingerprint 83e9e13f2a9497f2b4f0ca6b338a2e98966cfd70f6864882f1525fea02114285.
def localCycle00174 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![0, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 20 1, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint 83f2df11569f5fa2539c1a18079923b0ec3bc90bb86bb1fd2878944f19f0d18f.
def localCycle00175 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -2, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 20 1, .triangle 1 0, .gapLower 1 0]

-- Cycle fingerprint 854f7d1835b1f699f7f021793f898a99bd57569e62cb395a362607a459aa2adc.
def localCycle00176 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .theta 5, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 0 5, .distance 2 5, .distance 5 6]
    constant := ![-1, 0, 0, 3, -3, 0, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 5 6, .thetaLower 5, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 3 2, .triangle 7 1, .triangle 30 0]

-- Cycle fingerprint 858a08f2f8ab16c36873df6fdc4d443b31063c97668cee7b9761fa84e9cf8d3d.
def localCycle00177 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 5, .distance 2 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 5, .distance 0 5]
    constant := ![0, -1, -1, 0, 0, 0, 0, 2, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, true, true, true, false, false, true] }
  origin := ![.triangle 7 1, .triangle 30 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 3 2]

-- Cycle fingerprint 85a11593691138c8c47c8790feaa1bf174ecc0deeabd31a1b3b5cdaf82563ae3.
def localCycle00178 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4]
    constant := ![0, -1, 3, 0, -3, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 4 2, .triangle 13 1, .triangle 29 0]

-- Cycle fingerprint 8641ba6f8cc8c8b39f8cbc03c1091d0206d7e052790d33206262bf356ff24322.
def localCycle00179 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 86658f9af7a8f8ff41452020a1bd3513a4a8a31ca33495bab52692c9614b6e29.
def localCycle00180 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3]
    constant := ![-1, 3, 0, 0, -3, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .gapLower 1 3, .triangle 23 1, .triangle 29 0, .gapLower 2 1]

-- Cycle fingerprint 86df220cb7807e36225862be3a00c6e7e60287fa71a67c0c8a5ba53b9c3eb41d.
def localCycle00181 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 23 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 8758b9fafb0e8aa643aab186730953167440a5fcc0f92703a26b341dd3a0921d.
def localCycle00182 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 2, .gapLower 1 4, .triangle 20 1]

-- Cycle fingerprint 88b06e12383d0b45f44c65be042d2cff94109b835df4e66d13a36b8cdda8481e.
def localCycle00183 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 16 2, .gapLower 1 4, .triangle 24 1, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 890bf1531bc69373d149dbe7e74cd025e2a6807d31da75bc1f9e9acb47f70e37.
def localCycle00184 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 0, 3, -1, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 8a77bc802ffb77031a66e92464cc3bdaf8d2264529bc76fdd20b124c64a0e525.
def localCycle00185 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, -1, -1, 0, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, false, false, true, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 7 2, .triangle 14 0, .triangle 30 0, .gapLower 2 2, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 8aa3a0ceb585358936433492e352e28a44e503829fe33015cd37938739af92e2.
def localCycle00186 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 30 2, .triangle 8 0, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 8e1a28db6875ae68b0f5545222eb216458fc8d37aea82d2442d8b2b48173466f.
def localCycle00187 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4, .distance 3 4, .distance 4 5]
    constant := ![0, -3, 0, 0, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 5 4, .gapLower 1 4, .triangle 4 2, .triangle 14 1, .triangle 30 0, .gapLower 2 2, .gapLower 4 0, .corridorUpper 3 4, .triangle 31 0]

-- Cycle fingerprint 8ed89c925717ec1f0c762f2c39b74e08efb5e5a58177a24422a920a93ed36b7e.
def localCycle00188 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 8f579fc1f3f883c65abfae81c6b1375d56ad48d69a1e928c9289ae35cd5d3c39.
def localCycle00189 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 24 2, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 22 2]

-- Cycle fingerprint 8f8017ab585073dd0934867f062689faa27fe8b170b0fd93b30b6a49b7d0177b.
def localCycle00190 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 22 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 9034dd51ced91c9d3ef0f40d597e1811da435399ce95d4e2627dbc6dda3a75f6.
def localCycle00191 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6]
    constant := ![-1, 0, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 22 2, .gapLower 1 3, .triangle 23 1]

-- Cycle fingerprint 907e1c6d02a1c94f69492af10021589b382fcd360bc03227b13b017b3393f7fa.
def localCycle00192 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4]
    constant := ![0, -1, 3, 0, -3, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .triangle 2 2, .triangle 12 0, .triangle 28 0]

-- Cycle fingerprint 91bc19565844ade036fd4e27b8758bde9fca52ea0e67379a95afb45bc7b71ce9.
def localCycle00193 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6]
    constant := ![0, -1, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 23 0, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 926985bd1f970f621dddd7bf2cc5ff07c7d1547342fd557fd1f0db94eec1b009.
def localCycle00194 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, -1, -1, 0, 0, -3, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, true, false, true, false, false, false] }
  origin := ![.triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 12 0, .gapLower 0 2, .triangle 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 92756ce6f90691be1b226b6a71a503b986a61c8499e1f421f295fe9888a467a8.
def localCycle00195 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 3, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint 9299395381ad03266d21436831ce123948d82eba42fc8bc40cf4eecbd340d23b.
def localCycle00196 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, -1, -1, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 94e9f7bed08ce16cd1ef048688e6bca0a9cdc453d7e826fb6ec206517c642c51.
def localCycle00197 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3]
    constant := ![2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false] }
  origin := ![.gapUpper 3 1, .triangle 33 1, .triangle 34 0, .triangle 28 0, .gapLower 2 1]

-- Cycle fingerprint 968dfa9d10f961a9f0046706a28fbeac28978f1ddbc35463622efda303289e18.
def localCycle00198 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 1 5, .distance 1 3, .distance 3 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint 970b46a49e71969dccdb3127d6767fc2df3e1745944b78c1ba3f4f3166294dff.
def localCycle00199 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6]
    constant := ![3, 0, -1, -1, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint 973b39efecf2047a4242802e37fe31e45adf6c84e253be2acf22a10a6410c50b.
def localCycle00200 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Cycle fingerprint 98a6703366e950e4864344ddf536f214d22eaf6847a04e283937c1c857624fc1.
def localCycle00201 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, 0, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 22 1, .triangle 19 1, .triangle 1 0]

-- Cycle fingerprint 98e76b9fc5a0dc26a5916ef54198df39bb27dd9763d877b2e69962582736ef03.
def localCycle00202 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 98f5d2bd7c0793ec744dbc333c229f9919eba9b7df8036ded7a1ef5403f5e5ca.
def localCycle00203 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 99d1cd70d39816b824312b490b15caa3763a5695aad5ffebc6e9298e8e3c0737.
def localCycle00204 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 6]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 6 5, .triangle 23 0, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint 9a7e9f48cfe1f578012ea81ea0cdd167151e6939976c45c42f491aa8e24dae58.
def localCycle00205 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, -2, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 22 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 9bed333052983854e641300db444c1ced20f8e30a42feabc51bd49bc2bc408b0.
def localCycle00206 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 2 5]
    constant := ![0, -1, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 24 1, .triangle 30 0]

-- Cycle fingerprint 9cdfe9d8e9af8253fa8e9f7bfed491020c3c5adcf3a3b61bbc49318be3a7036c.
def localCycle00207 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .distance 1 2, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![-1, 0, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .triangle 17 2, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 9fbbd67a5a7a19d9f77dd042fa339885e7fbe48d6f303dd6c1bd2e6dc2b381a2.
def localCycle00208 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-3, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 2 2, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 9fdeb658a4ec565c5092c259c6f7a8ea60ed6d90396821ea806da35c0c3bb3ea.
def localCycle00209 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5]
    constant := ![-1, -2, -2, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1]

-- Cycle fingerprint 9fe4b280c92f24eb54e5abd7c12de2ab6544e45086b10b8680c11e7a498bd8c6.
def localCycle00210 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 19 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a05faa4cba0286962d2c4ba58c50fdeba18755230ed43bd378e4f93c6a68efa1.
def localCycle00211 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 22 2, .gapLower 1 3, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint a0ce0a551b82435ddc9a9f88e3419685410316ac60f9b2ab14c4e136d2b54c21.
def localCycle00212 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .triangle 22 0, .triangle 19 1, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint a3f672e3c851bdac6bbee25f1aec123ecb825508142f5590bc2e3bb6864747da.
def localCycle00213 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 4 5, .distance 2 4, .theta 4]
    constant := ![3, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .gapLower 1 4, .triangle 3 2, .triangle 12 1, .triangle 28 0, .gapLower 4 0]

-- Cycle fingerprint a4f92db99d01c5f146eaab8c359a0b784a756fbd14285d5de880895032cc05cb.
def localCycle00214 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5]
    constant := ![0, -3, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0]

-- Cycle fingerprint a8e949f63df8cb1702afa8f6587eef8363eb28eeb948c96abb66e4ff77dd8659.
def localCycle00215 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 5 4, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0]

-- Cycle fingerprint a930409d953adbb1823eeda0c6dea6413b0da231debf6ec24532e345e3b22bcc.
def localCycle00216 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3]
    constant := ![-2, -2, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0]

-- Cycle fingerprint a9b981870b15a9ecf282c044d4f9fbc4ced794888dd294c287eb7ebe462243e0.
def localCycle00217 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 5 4, .triangle 22 2, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint aa044c742ead9342de58b1e5b49ff0570d5d367898f397e14a5c9b48848b0fee.
def localCycle00218 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .theta 1, .distance 1 2, .distance 1 5]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 17 2]

-- Cycle fingerprint aa5d8fc73799c4f6f43937a126a31f7ed78df362071661fecbbc35838eb60c34.
def localCycle00219 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 3, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint aa90497857847e3abf7d703c2cb89c85a633c6ecf7d79365288c9ccfd60d0011.
def localCycle00220 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 1 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint ab238e0a3220d2194c44060cce99cf1c15cbfac71a1c8b2d082c22c2b0640695.
def localCycle00221 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 0 4, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![0, 2, -2, 0, 0, -1, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint abf42161645a9dd044edee6ddd457810b1242d2a909e834e36afd3f96fe2593e.
def localCycle00222 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 0]

-- Cycle fingerprint abf4e6aaa081becc089bfbf7b567f10d5e2e819c7a38342129efe7bd1ef01cfb.
def localCycle00223 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint ac1369a14020e0a1f3d65d71e5d171c4189476718ce42ba86dd6a86329cea200.
def localCycle00224 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 3, .triangle 20 1, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint ad421a8cc8f1754786aed55c472cc9a83c50dc072b53d770c3cf6b6cf86db485.
def localCycle00225 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 5]
    constant := ![3, -1, -1, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 1 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint b0d9a3403ef9597f341d90e34f8b5d4da1cac878032679bd0f8014fa6c496135.
def localCycle00226 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 2 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true, false, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint b13e3ca157dc9975e2f6bf16ad8cb4724aaff257cc75fd092f40bf224a3562ca.
def localCycle00227 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint b21b163928d9b7c341aa5cc741d286960a60339cc29312b4982edac37009cc3e.
def localCycle00228 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, -1, 3, -2, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 2 2, .triangle 13 0, .triangle 34 1]

-- Cycle fingerprint b2aaf57f234195aa71c4b9ea633fdbb2a37c47385a0d1ad0d353826ab2351fb9.
def localCycle00229 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 4, .distance 2 4]
    constant := ![0, 0, -1, 3, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, true] }
  origin := ![.triangle 28 2, .triangle 26 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 2 2, .triangle 6 1]

-- Cycle fingerprint b3260865f4f3316a887447e2f6cedc28b3b8a9de53d9c6b1a21bbb36871d38cc.
def localCycle00230 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 2, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint b3d835bd9cae10164ac6d955e00542a8964feebcccd3112568aac97396d3a04f.
def localCycle00231 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 30 2, .triangle 8 0, .triangle 5 2, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint b530ca181000d395fec88dbbc3238a8b014abb8ee54cbe0242bdda6ae076577c.
def localCycle00232 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 3 5]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 5 4, .triangle 22 0, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint b5907bf1721a33dd4b4237736967fd3cd829fdc1d34846c2a8ef5ec876a97fe9.
def localCycle00233 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, 0, -1, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint b68ecd7e9adfd0f51057d051a73b9a300d4efd3117b7146d2fb59feb7e704124.
def localCycle00234 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2]
    constant := ![3, -3, 0, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 23 1, .triangle 22 2, .triangle 20 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2]

-- Cycle fingerprint b6a58d5c44dd572499f6711dc928a618e6f6c385eed4183b473ef7553a1aef59.
def localCycle00235 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5]
    constant := ![-1, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 22 0, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1]

-- Cycle fingerprint b6a9e3398d48323455143adf4f4813bce53a63c13149d95814f42d3967585f8b.
def localCycle00236 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -2, 0, -2, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 3 2, .triangle 12 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint b6aa2bdd71fa79988cfcb386083b4ff23e84c643a0b10d8b251ea82abb29d13b.
def localCycle00237 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .theta 4, .distance 4 6, .distance 3 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 4 5, .distance 2 4]
    constant := ![0, 4, -1, 0, -3, 0, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.gapLower 4 0, .gapLower 4 6, .triangle 32 0, .triangle 19 2, .gapLower 1 3, .triangle 3 2, .triangle 12 1, .triangle 28 0]

-- Cycle fingerprint b6d3ec466f80a90ecf9f288e887efa4aa2b277c8a0c98de6819fbaf9608bf62f.
def localCycle00238 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -1, 0, -2, 0, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .gapLower 6 3, .gapLower 1 4, .triangle 22 1, .triangle 19 1, .triangle 1 0, .gapLower 1 0]

-- Cycle fingerprint b733a7d95b2d18ff5f9f33f85ec644b1c6df21524dbb16934bcb5b2bb4a3e635.
def localCycle00239 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -2, -2, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 2, .triangle 14 1, .triangle 30 0, .gapLower 2 2, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint b94351ae4a8257e7a5d263f5af79040167e9469530fc5b52fea3eca95a357053.
def localCycle00240 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 6, .distance 1 3, .distance 3 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint b9c29007a7a164d16f5b0aa64d3d635e58dbd422c95a190600cc8e79414c5feb.
def localCycle00241 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint b9f5f382cfbecf108fdbb84beb488e5c6ad9f3ae403395e59ff40c7b2a5443c2.
def localCycle00242 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 0 5, .distance 0 3, .distance 0 1, .theta 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6]
    constant := ![-1, 0, 0, -2, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.triangle 14 0, .gapLower 0 2, .triangle 1 1, .gapLower 1 0, .gapLower 1 6, .triangle 16 2, .triangle 22 2, .triangle 24 0]

-- Cycle fingerprint ba0d83ded1e1c5c50290195697efc990bf958aca5e3db86fff69833438e10a0f.
def localCycle00243 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 1 4]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 6 5, .triangle 23 0]

-- Cycle fingerprint bb24bfb52eb657457465b9ca1d2ae8bce56fbc84c60eb4636e2463c95ed82b72.
def localCycle00244 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 24 1, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint bc12b5a6ab4d8b4339e2dc86964cb8613828480785bb683246b8766dea7896b7.
def localCycle00245 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 0 4, .distance 2 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -3, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 2 2, .triangle 6 1, .triangle 29 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint bc53d5b3b035f928b436abceb40f2dd0fcf31cb767596892d60be37bab900fa2.
def localCycle00246 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6, .distance 2 4]
    constant := ![0, -1, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 23 1, .triangle 29 0]

-- Cycle fingerprint be15e555bf311db0c94fcd23da51cb892007fbed139f38712824d1099d31016d.
def localCycle00247 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 3, .distance 3 5, .theta 5]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 2, .triangle 8 0, .triangle 5 0, .triangle 26 0, .gapLower 5 0]

-- Cycle fingerprint be200fdb00a368efd12b49e8d25d4811e341f04207220135407dddf4dc725fd7.
def localCycle00248 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 1 5]
    constant := ![-2, 0, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 23 1, .triangle 19 1, .corridorLower 1 3, .gapLower 1 6, .triangle 17 2]

-- Cycle fingerprint c0cb85f9215f83a567a86106a203b7c049cfcd34a4500b144871d452c4e41101.
def localCycle00249 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, -2, 0, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 20 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint c1807434527fb5780df61aea12456c6436c7a69faa72b565fc50b5b9969cd0ef.
def localCycle00250 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint c187e8e013e561930139c48feea8512fcf821678b3cce0c7699ff5fc4873f1ad.
def localCycle00251 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 23 2, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint c1a4faf179dc8fc60a363681584f6f1e6ca0493ca2373a33480cbb1ca18be631.
def localCycle00252 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, -1, 0, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 34 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint c20c290c562ebadc2db6d9f325f1701e9b054dff3b43d38d1f45105035bfd1d9.
def localCycle00253 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 26 1, .corridorLower 2 3]

-- Cycle fingerprint c389bd8b7c34837c72474769048fea0c3b04d569dbda2c10d65390279526f0fa.
def localCycle00254 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint c3ed6b20c12c2f3febd613afdab654eacc59f50cbc022efc9db2ca0b73abe336.
def localCycle00255 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 2, .triangle 14 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint c3f916726cf08755e8baad01b521627a99115da8135e2e94235019ba4cbe8d2b.
def localCycle00256 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 1 2, .distance 1 4]
    constant := ![0, -2, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 20 1, .corridorLower 1 3, .gapLower 1 6, .triangle 16 2]

-- Cycle fingerprint c3fd8164e987bddffd4f595c33ea128ea21e13f7ce778fde9a501d59602220e5.
def localCycle00257 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6]
    constant := ![-1, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint c44c067dc3a0d7748d9ecdb335d6dc3fe63c5ad8cd0bad51c52a57083fbcbd7f.
def localCycle00258 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4]
    constant := ![0, -3, -1, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .triangle 22 0]

-- Cycle fingerprint c46b510de6578010c96d6a9fff74cfff2a70420ab404317d79c2ab653111581d.
def localCycle00259 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 2]

-- Cycle fingerprint c509b1e07c8de41f56154914ba0c3af49c564f0f59050e59e533035dd8726c31.
def localCycle00260 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 16 2, .gapLower 1 4, .triangle 24 2, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint c580eb741dd8ff97b99541354baf25da0af15cbc6654d9df08c3d8bbb8dfc2cd.
def localCycle00261 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 22 2, .gapLower 1 3, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint c597f235b9ec9c5b5e2d2dd25844070d6c5e7f4d35d8433dc8dd7e8029c5b175.
def localCycle00262 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-2, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint c59b2ae221131ca1c0fa787476e152d6e1b6b6c46409865dae1374feab273c13.
def localCycle00263 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint c5e0740d2fe9fa119af8488bca17be62ae6a236f73bbcbeb99b1e7785269ce69.
def localCycle00264 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint c8a81d0f9a95684f7198c4eca483ab79eca489bf58999b60891c352143b081c9.
def localCycle00265 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 18 2, .gapLower 1 4, .triangle 22 2, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint cb11f078cb63df346bf6d3ee044f8f699c1de521b1c36522e4402f1280d89254.
def localCycle00266 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint cbd561fe824fd74b3efb7522bf56bb43ac35c13ffc238e1bd80f53d32ea5aea5.
def localCycle00267 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![0, 2, -2, 0, 0, -1, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, false, false, true, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint ccb2762e0d8d1d6185d5f4a22d2081fdb00133f4ea8668763233848133523d05.
def localCycle00268 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 22 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint cd6949d567b2295063cd83c0ad325753dc9529171faa22da0a9b3a01d71c98f5.
def localCycle00269 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint ceca543f0dcca6529696c113005b45be2d4c061a337988f993d8d894b36ee046.
def localCycle00270 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .theta 1, .distance 1 2, .distance 1 4]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .corridorLower 1 5, .gapLower 1 6, .triangle 16 2]

-- Cycle fingerprint cf7b0672276222d6e80e6f96a80cfdc9f25aa35da08be785bf31fdfbe8059bbf.
def localCycle00271 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint cf8208ea209c9085140f56b733afc9b5a28006596e8e7de6154ae8dc30649464.
def localCycle00272 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .triangle 19 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint cf9e39ca87d6de2e02187308828554d582a1451291f43231f083da6bae4cc233.
def localCycle00273 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -2, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .triangle 19 1, .triangle 1 0, .gapLower 1 0]

-- Cycle fingerprint cfc0408014d11a712c9822878b32b5f540992f0a17d05ad38eac8e1fdafc9ebb.
def localCycle00274 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint d0f9767f684699e7519b1d1045f311fb9a4ef0a671838cb990996966483543a1.
def localCycle00275 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint d19ed8ed589c29cabf9cf321132c031117d4c6015f18c7ece2edbe5f60aecaf5.
def localCycle00276 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6]
    constant := ![3, -1, -1, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .triangle 1 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint d2230cfc1ec9c652e85584858d9498910a929d5e09f4648927d6f30aaa0626d1.
def localCycle00277 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 9 2, .triangle 12 0, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint d2666dd4ec83606a6ebf73546899001b855d82824db28ddd89b0028731656922.
def localCycle00278 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 1 4, .triangle 22 1]

-- Cycle fingerprint d2f77b1d1783144920013f28cd83fc68e1c440884f5a6b953b78c78c5f1e2c2c.
def localCycle00279 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 5, .distance 4 5]
    constant := ![-1, 0, -1, 3, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 3 2, .triangle 12 1]

-- Cycle fingerprint d3e7cc20abaa2b1d27553070e7d87db18982f6804ac83d84ba4906c55cb10d1a.
def localCycle00280 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint d4a15ce92cd7b3f101d446bb11628a1f66569f3ed464043d620aad625ce1c78f.
def localCycle00281 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 4, .distance 2 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .zero, .theta 1, .distance 1 2, .distance 1 4]
    constant := ![0, 0, -1, 0, -1, 0, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, false, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 6 1, .triangle 29 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaLower 3, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint d4f1c1f99901cb81b6e093d38dfb90030e9580c26edd322e52b0a97d2ab47927.
def localCycle00282 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 3, .triangle 20 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint d620d4a0fbcedac09984abb948e008fedcc9b326a3daa34becf70f264fbb5360.
def localCycle00283 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 6, .distance 1 4, .distance 4 5]
    constant := ![-1, 0, -1, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 23 1, .triangle 22 0]

-- Cycle fingerprint d63901a4c2a64dc3a419c9b4675a289e45494c4447ef93945205081c793e706d.
def localCycle00284 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 1 2, .distance 1 4]
    constant := ![-2, 0, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 24 1, .triangle 20 1, .corridorLower 1 3, .gapLower 1 6, .triangle 16 2]

-- Cycle fingerprint d6f9e2c62218742f76becf403559c515b5f61ecd2f427cf762601c963a754877.
def localCycle00285 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .theta 1, .distance 1 2, .distance 0 2, .distance 2 5, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 1 3]
    constant := ![-1, 2, 0, -1, -1, -1, 3, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorLower 1 3, .gapLower 1 6, .triangle 0 2, .triangle 7 0, .triangle 30 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 2]

-- Cycle fingerprint d7931389e17c9d43bffce3a8910c86c057142abee0570370220cce04a3d09979.
def localCycle00286 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint d88d93c2e8d1d3499a158185332fce8497196071f0103cc6bcfe6e228b724869.
def localCycle00287 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 6, .distance 1 4, .distance 4 5]
    constant := ![-1, 0, -1, 0, 2, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 18 2, .gapLower 1 4, .triangle 22 0]

-- Cycle fingerprint d8a9ee1ba96ec3ec663f835c87dbd7663cd170c9b3207d3d5ee035a66413d1f7.
def localCycle00288 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 4]
    constant := ![4, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 22 0, .triangle 23 0, .triangle 29 2, .triangle 8 0, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 25 0, .gapLower 4 0]

-- Cycle fingerprint d8c2358c626e5eea153d1d91547ed75a747ca8baf681d2977c947cf5b2dbae2a.
def localCycle00289 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, -1, 0, 0, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .gapLower 1 4, .triangle 22 1]

-- Cycle fingerprint d967b4869fecf9f6845802ad4100552f22e5638beab30f14a95435dbf29eb6fa.
def localCycle00290 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4]
    constant := ![-2, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0]

-- Cycle fingerprint d993a2a12c104d318da621e529a0f0dfa020c7ae19edf177ed28ec7bd85dcab5.
def localCycle00291 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 5, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 6]
    constant := ![0, -2, 0, 0, -1, 0, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false, true, false, true] }
  origin := ![.triangle 23 1, .gapLower 1 3, .triangle 3 2, .triangle 12 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 18 2]

-- Cycle fingerprint d9b490ae15c4ed10c80dd06853f04da26db025438d3d00ccd3f5e1e3bf4571f8.
def localCycle00292 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint da58a175bede7acf9ee3dbe920177d39fcf34b0bc7484413154340a31f3b04b8.
def localCycle00293 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, -1, 0, -1, -3, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint da6e787550d972cd0fd385400e9b04af56caf74e854febaeadb848c55ad8a1c5.
def localCycle00294 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .distance 1 2, .distance 1 5, .distance 0 5, .distance 5 6]
    constant := ![-1, 0, -1, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 3 2, .triangle 14 0]

-- Cycle fingerprint dbdf8e8b577f97fa36d84f1f96a545d6197f0861b72ed892b054f8e5d23957f8.
def localCycle00295 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint dcc960a324581a7a58781ee089dc11a5a56ca262507309b149371b0a72360115.
def localCycle00296 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 5]
    constant := ![0, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 19 1, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 2]

-- Cycle fingerprint dd8175dfb342f06ff51c07c27f0680e94b2c97989a793b255e9e3944bab6e1c9.
def localCycle00297 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 5, .distance 4 5, .distance 2 4]
    constant := ![0, -1, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .gapLower 1 3, .triangle 22 1, .triangle 28 0]

-- Cycle fingerprint de66af9f13f823a5db3b8935fc6c7f6cfbce5d152ea493e16ed5947dd9f6403c.
def localCycle00298 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, -1, 0, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 23 0, .triangle 34 1]

-- Cycle fingerprint df07a7b2ccae19e20e6f0e23a75c2fdb2e02c97b8ca97e527a5e9d720d0d2fc8.
def localCycle00299 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -2, 0, -2, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 22 2, .gapLower 1 3, .triangle 4 2, .triangle 13 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint df33c5b2c86c9f2f23c3d7666ed60b7aec0bbbfb643b691654b932797a89330a.
def localCycle00300 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .distance 1 2, .distance 1 4, .distance 4 5, .distance 4 6]
    constant := ![-1, 0, 0, -2, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.triangle 13 0, .gapLower 0 2, .triangle 1 1, .gapLower 1 0, .gapLower 1 6, .triangle 16 2, .triangle 22 0, .triangle 34 2]

-- Cycle fingerprint dfac2060eb619c87f26398cf714e631f663b0f42df17e06dfbc7099ad23a3ebc.
def localCycle00301 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 22 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint e031c7daa302223b6e911ab67c86db8e30dbb847d2227016d791777fa712783e.
def localCycle00302 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint e0fe4b252d69f692644cd9398dfb4ce802730a1879eed1282eee862053a3d468.
def localCycle00303 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![0, -1, -2, 0, 0, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 1, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint e11325426596589b4dc2ae67badea501ef2f9bbb43ccc5de6685b887dbf05fd7.
def localCycle00304 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, -1, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint e1a68970e4bad34ec968816c9dc32817f7edd74936d94e4ea9ecc213420cdca1.
def localCycle00305 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint e1ab0fefc84c9d37613a7b81fa9b8f9b2698ef7615eb722e4c94c3280abb4051.
def localCycle00306 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -2, 0, -2, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 3, .triangle 3 2, .triangle 12 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint e31cd20ac8a54d1eefce3219478e06ab846a5ba96bb6fcda5299633ee15eca88.
def localCycle00307 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0]

-- Cycle fingerprint e343d47f4374fb700efb0043cb0da89362ae755879ac9022186f0178a258fc78.
def localCycle00308 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint e453da6aa5fccb9e97f3eab0541e1bc95a9d759528a958d3d3ed808485a8e6d5.
def localCycle00309 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 0, 3, 0, -1, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint e4abaf9adaf0392c5f4c88e39bb9302142241e2b32c29117c8676ecc8c52bfe4.
def localCycle00310 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 4 5]
    constant := ![-1, 0, -1, 0, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 6 2, .triangle 12 0]

-- Cycle fingerprint e500149105668b02d1215592906909673c202005a288863e67887799111a57dd.
def localCycle00311 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint e53797ba7943d349444233a71cde9c1604b5ebec9cce8fd43f2d0c1b7de144d3.
def localCycle00312 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e591d4987cbe3f87af8b07167894938dd376e082ff9f3c10f4a71defa78a9878.
def localCycle00313 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .triangle 22 1, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e62a037ee093c4b47a3abd985fa848fa8a2a22102500950292bf882aaed7814f.
def localCycle00314 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 4, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 2 2, .triangle 6 1, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint e6a6903f74d0c0eb5551bc5182ab9a4f14795a870b8d9c4294cb342549a224e0.
def localCycle00315 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 4, .distance 0 5, .distance 5 6]
    constant := ![-1, 0, -1, 3, -2, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 2 2, .triangle 12 2, .triangle 14 0]

-- Cycle fingerprint e71d02aa8f936ed1a17f46b11e48ec4b044b1e6ae60e2dabc59ea955dc607f36.
def localCycle00316 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 0, 3, -1, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint e7e5ddf17b841331385caa13269d0526b15502ef19af23208460487c3eb5e3ab.
def localCycle00317 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, 0, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 23 1, .triangle 19 1, .triangle 1 0]

-- Cycle fingerprint e836966a218ac023aeb483f0d274e47069b6f03a08594103177f2d656d4a5088.
def localCycle00318 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint e8cc1e235c0358f3a3b088656320dfa9a540338aae36b1a4c7f5ab48455d3bd1.
def localCycle00319 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint e8d1fa286367c572ec9837dac94a2c8b6f74f2526cc074b0a7044dff45bed8be.
def localCycle00320 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 0 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![0, 2, -2, 0, -1, 0, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 2 2, .triangle 13 0, .triangle 34 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint e962e7b75adecb6d842ca78685ca057947f94117ad1e7b5d46d4397bef65572d.
def localCycle00321 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6]
    constant := ![-1, 0, -1, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 22 2, .triangle 24 0]

-- Cycle fingerprint e9e326c259aac1483b9b6d93160550c608ed3cc8ea4d3c583f260f09456be2d5.
def localCycle00322 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .theta 1, .distance 1 2, .distance 1 4]
    constant := ![0, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 22 2, .triangle 24 2, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 16 2]

-- Cycle fingerprint ea7c36866b3d03c32223bf8aa19b04286b092ca1f5cf2b268491a0a271fa80ae.
def localCycle00323 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .gapLower 6 3, .gapLower 1 4, .triangle 22 1, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1]

-- Cycle fingerprint eab7ca1c92a77833364d7e18d86d7ebf6bad84ecfee8aa1da8bc6458400f9176.
def localCycle00324 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint eb122f6c2aaf5bb91c6d4b28ced211cf2079c904001af528dde5501b9514609f.
def localCycle00325 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .theta 0]
    constant := ![0, 0, 3, -1, 0, -1, 0, -1, -3, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint ebfd76ae3e3adaa1042c1224826199d9c7587106ee3e9890481b485b314add19.
def localCycle00326 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0]

-- Cycle fingerprint ed33b964f9147ed4b2cd4e75546cda30ab16b2c0cf14779fa1ae591a0264fbda.
def localCycle00327 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint ed73c6f47f106d003db15f9fbdb6e1463dc967728648757979d041f5590c523f.
def localCycle00328 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint edafea539b42b206123bf74a2e4923ffbe21c357208850addf8cdc007350a74b.
def localCycle00329 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint eefd7f492dd6b90d6fa930aa925c78b862e5d83925c3c7095967b54e03e81e8f.
def localCycle00330 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-2, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 24 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint f078f940ae279e82908da92b53e1eff7a072aac79f40180b44dce46a1aad607e.
def localCycle00331 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 23 1, .triangle 22 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint f0f091fcf46e3ef8fdbfaadc1700c6186a654385d49567758436495c19318ee8.
def localCycle00332 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 0 4, .distance 4 5]
    constant := ![-1, 0, -1, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 2 2, .triangle 12 0]

-- Cycle fingerprint f3d89b9938c3c68be241991f2258a3b7b9751dca573797121e432b68e8bc8075.
def localCycle00333 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 6, .triangle 16 2, .triangle 22 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint f410001a2a3236e41d61c9981f6454ad74545215c8ca8e0419bb7567a06931d1.
def localCycle00334 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4, .distance 3 4, .distance 4 5]
    constant := ![0, -2, 0, 0, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 22 2, .gapLower 1 4, .triangle 4 2, .triangle 14 1, .triangle 30 0, .gapLower 2 2, .gapLower 4 0, .corridorUpper 3 4, .triangle 31 0]

-- Cycle fingerprint f416479dfada4463a5b529efd501815a86709521f019b188ff7d617f8e186f94.
def localCycle00335 : Cycle where
  length := 6
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 5, .distance 5 6]
    constant := ![-1, 0, -1, 3, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .triangle 24 0]

-- Cycle fingerprint f5fdf5f3618f6d6847724acb9de258aa6dff12dae7bce4bd734a8dd1b5de4b27.
def localCycle00336 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, -2, 0, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 17 2, .gapLower 1 4, .gapLower 1 3, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint f64cc9db9496f7e40ad14b22424c7a1a6aa3a8eb449c10d7fe9399b81cdcce29.
def localCycle00337 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 17 2, .gapLower 1 4, .triangle 23 1, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint f67a04328da11dd289efab297221fa7098c6a54d82e746fa98b77391a1c81e3d.
def localCycle00338 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 3, .distance 3 6, .distance 1 6]
    constant := ![-2, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .gapUpper 3 3, .triangle 21 2]

-- Cycle fingerprint f6f1040017a894e5035c3236074ed93f60960d5683f8187b044db3ae0a73ae12.
def localCycle00339 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, -2, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 23 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint f71b4cda2aebd5fd15f4d1ca438e42bc7a326cc71a6139ba5a71ece5ce06ff85.
def localCycle00340 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 0, .triangle 28 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint f881bb50dc797b002b2c22edde4e29a02ae5d925eeaaafa66414e80a0aadd78b.
def localCycle00341 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![-2, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 20 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint f95f39cfaa4d1a9543d43c3a3c327aa79648ce624d9c7d295f9e0a36ef0f71e6.
def localCycle00342 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint f988536ed773404c1c0b91bee9caca6d72c82cf5884eedf2e72f2b13bcc3368d.
def localCycle00343 : Cycle where
  length := 10
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6]
    constant := ![-1, 0, 0, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 24 0, .triangle 22 1, .triangle 19 1, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint faa01917f1bd31bd733257110133a235b05d0cf965ff8a5e464ec41cdef78ad6.
def localCycle00344 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-1, -2, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .gapLower 6 4, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint fbd531a52cc8d18c1d95f64224747deb6e3f296f750ad68e81d32b2daecd6e76.
def localCycle00345 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, -2, 0, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 18 2, .triangle 23 1, .gapLower 1 3, .triangle 22 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint fc025a242b51ec0103af12f67cae693ba7874750b922c547daebab6046064290.
def localCycle00346 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint fc02bb9bb7145eac7e56caaec55f388dcb7f577d80db4737ef95b90fa88cf3c7.
def localCycle00347 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2]
    constant := ![3, -2, 0, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2]

-- Cycle fingerprint fc3b4792351d4460ae0cc339acf212451a5e162b07cabafda0dc39af7939d8b5.
def localCycle00348 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint fc441bb643445e03e9d3545717f308396463f65381847c8f20eab276557104a0.
def localCycle00349 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -1, -1, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint fc5a053f2633fed0a94e98cf7bbdb08c0400fdc353ed16bf7d2e2871d0d831ad.
def localCycle00350 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint fc9cd4c48d6891fac591949340bf9050f55dbf872c49f7fbb25d3b7418641bb7.
def localCycle00351 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6]
    constant := ![-1, 0, -1, 3, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 2, .triangle 13 1]

-- Cycle fingerprint fcb12ff885d1c96968255e5bf55b5209c38c8493645c542ace0284d32f2dff44.
def localCycle00352 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, -2, 0, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 18 2, .gapLower 1 4, .gapLower 1 3, .triangle 20 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint fd89e8a67205ac0fda036012beea0c5cb14eca8f41d86837fb3e77bfaf73497d.
def localCycle00353 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6]
    constant := ![-1, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2]

-- Cycle fingerprint feaf82394c0c2c1a3247a136407523d5c767081b5e05dbd8425b84b6a9905800.
def localCycle00354 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint feeeb31fdd47c41a38feb7092641fbcf1b36ee9c128add0571574af8bc5ef1e3.
def localCycle00355 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6]
    constant := ![0, -1, -1, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint ffdea6bedb254e95ad2501e22d536e11d53342ad847844d39c20da12b7b8d752.
def localCycle00356 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 6 2, .triangle 12 0, .triangle 34 0, .triangle 30 2, .gapUpper 2 4]

def library : Library := fun id => if id < 178 then (if id < 89 then (if id < 44 then (if id < 22 then (if id < 11 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 8 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none))) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none))))) else (if id < 16 then (if id < 13 then (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none)) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none)))) else (if id < 19 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none))) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)))))) else (if id < 33 then (if id < 27 then (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)))) else (if id < 30 then (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))))) else (if id < 38 then (if id < 35 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none)))) else (if id < 41 then (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none))))))) else (if id < 66 then (if id < 55 then (if id < 49 then (if id < 46 then (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none)) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)))) else (if id < 52 then (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none))))) else (if id < 60 then (if id < 57 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none)))) else (if id < 63 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none))) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)))))) else (if id < 77 then (if id < 71 then (if id < 68 then (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)))) else (if id < 74 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none))) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none))))) else (if id < 83 then (if id < 80 then (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none))) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none)))) else (if id < 86 then (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none))) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)))))))) else (if id < 133 then (if id < 111 then (if id < 100 then (if id < 94 then (if id < 91 then (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none)) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)))) else (if id < 97 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none))) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none))))) else (if id < 105 then (if id < 102 then (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)))) else (if id < 108 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none))) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)))))) else (if id < 122 then (if id < 116 then (if id < 113 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none)) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none)))) else (if id < 119 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none))) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none))))) else (if id < 127 then (if id < 124 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none)))) else (if id < 130 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none))) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none))))))) else (if id < 155 then (if id < 144 then (if id < 138 then (if id < 135 then (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none)))) else (if id < 141 then (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none))) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none))))) else (if id < 149 then (if id < 146 then (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none)) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none)))) else (if id < 152 then (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none))) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none)))))) else (if id < 166 then (if id < 160 then (if id < 157 then (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none)) else (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none)))) else (if id < 163 then (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none))) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none))))) else (if id < 172 then (if id < 169 then (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none))) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id = 171 then some localCycle00171 else none)))) else (if id < 175 then (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none))) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none))))))))) else (if id < 267 then (if id < 222 then (if id < 200 then (if id < 189 then (if id < 183 then (if id < 180 then (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none)) else (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none)))) else (if id < 186 then (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id = 185 then some localCycle00185 else none))) else (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none))))) else (if id < 194 then (if id < 191 then (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none)) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id = 193 then some localCycle00193 else none)))) else (if id < 197 then (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none))) else (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none)))))) else (if id < 211 then (if id < 205 then (if id < 202 then (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none)) else (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id = 204 then some localCycle00204 else none)))) else (if id < 208 then (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none))) else (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id = 210 then some localCycle00210 else none))))) else (if id < 216 then (if id < 213 then (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id = 212 then some localCycle00212 else none)) else (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none)))) else (if id < 219 then (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id = 218 then some localCycle00218 else none))) else (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id = 221 then some localCycle00221 else none))))))) else (if id < 244 then (if id < 233 then (if id < 227 then (if id < 224 then (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id = 223 then some localCycle00223 else none)) else (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id < 226 then (if id = 225 then some localCycle00225 else none) else (if id = 226 then some localCycle00226 else none)))) else (if id < 230 then (if id < 228 then (if id = 227 then some localCycle00227 else none) else (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id = 229 then some localCycle00229 else none))) else (if id < 231 then (if id = 230 then some localCycle00230 else none) else (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id = 232 then some localCycle00232 else none))))) else (if id < 238 then (if id < 235 then (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id = 234 then some localCycle00234 else none)) else (if id < 236 then (if id = 235 then some localCycle00235 else none) else (if id < 237 then (if id = 236 then some localCycle00236 else none) else (if id = 237 then some localCycle00237 else none)))) else (if id < 241 then (if id < 239 then (if id = 238 then some localCycle00238 else none) else (if id < 240 then (if id = 239 then some localCycle00239 else none) else (if id = 240 then some localCycle00240 else none))) else (if id < 242 then (if id = 241 then some localCycle00241 else none) else (if id < 243 then (if id = 242 then some localCycle00242 else none) else (if id = 243 then some localCycle00243 else none)))))) else (if id < 255 then (if id < 249 then (if id < 246 then (if id < 245 then (if id = 244 then some localCycle00244 else none) else (if id = 245 then some localCycle00245 else none)) else (if id < 247 then (if id = 246 then some localCycle00246 else none) else (if id < 248 then (if id = 247 then some localCycle00247 else none) else (if id = 248 then some localCycle00248 else none)))) else (if id < 252 then (if id < 250 then (if id = 249 then some localCycle00249 else none) else (if id < 251 then (if id = 250 then some localCycle00250 else none) else (if id = 251 then some localCycle00251 else none))) else (if id < 253 then (if id = 252 then some localCycle00252 else none) else (if id < 254 then (if id = 253 then some localCycle00253 else none) else (if id = 254 then some localCycle00254 else none))))) else (if id < 261 then (if id < 258 then (if id < 256 then (if id = 255 then some localCycle00255 else none) else (if id < 257 then (if id = 256 then some localCycle00256 else none) else (if id = 257 then some localCycle00257 else none))) else (if id < 259 then (if id = 258 then some localCycle00258 else none) else (if id < 260 then (if id = 259 then some localCycle00259 else none) else (if id = 260 then some localCycle00260 else none)))) else (if id < 264 then (if id < 262 then (if id = 261 then some localCycle00261 else none) else (if id < 263 then (if id = 262 then some localCycle00262 else none) else (if id = 263 then some localCycle00263 else none))) else (if id < 265 then (if id = 264 then some localCycle00264 else none) else (if id < 266 then (if id = 265 then some localCycle00265 else none) else (if id = 266 then some localCycle00266 else none)))))))) else (if id < 312 then (if id < 289 then (if id < 278 then (if id < 272 then (if id < 269 then (if id < 268 then (if id = 267 then some localCycle00267 else none) else (if id = 268 then some localCycle00268 else none)) else (if id < 270 then (if id = 269 then some localCycle00269 else none) else (if id < 271 then (if id = 270 then some localCycle00270 else none) else (if id = 271 then some localCycle00271 else none)))) else (if id < 275 then (if id < 273 then (if id = 272 then some localCycle00272 else none) else (if id < 274 then (if id = 273 then some localCycle00273 else none) else (if id = 274 then some localCycle00274 else none))) else (if id < 276 then (if id = 275 then some localCycle00275 else none) else (if id < 277 then (if id = 276 then some localCycle00276 else none) else (if id = 277 then some localCycle00277 else none))))) else (if id < 283 then (if id < 280 then (if id < 279 then (if id = 278 then some localCycle00278 else none) else (if id = 279 then some localCycle00279 else none)) else (if id < 281 then (if id = 280 then some localCycle00280 else none) else (if id < 282 then (if id = 281 then some localCycle00281 else none) else (if id = 282 then some localCycle00282 else none)))) else (if id < 286 then (if id < 284 then (if id = 283 then some localCycle00283 else none) else (if id < 285 then (if id = 284 then some localCycle00284 else none) else (if id = 285 then some localCycle00285 else none))) else (if id < 287 then (if id = 286 then some localCycle00286 else none) else (if id < 288 then (if id = 287 then some localCycle00287 else none) else (if id = 288 then some localCycle00288 else none)))))) else (if id < 300 then (if id < 294 then (if id < 291 then (if id < 290 then (if id = 289 then some localCycle00289 else none) else (if id = 290 then some localCycle00290 else none)) else (if id < 292 then (if id = 291 then some localCycle00291 else none) else (if id < 293 then (if id = 292 then some localCycle00292 else none) else (if id = 293 then some localCycle00293 else none)))) else (if id < 297 then (if id < 295 then (if id = 294 then some localCycle00294 else none) else (if id < 296 then (if id = 295 then some localCycle00295 else none) else (if id = 296 then some localCycle00296 else none))) else (if id < 298 then (if id = 297 then some localCycle00297 else none) else (if id < 299 then (if id = 298 then some localCycle00298 else none) else (if id = 299 then some localCycle00299 else none))))) else (if id < 306 then (if id < 303 then (if id < 301 then (if id = 300 then some localCycle00300 else none) else (if id < 302 then (if id = 301 then some localCycle00301 else none) else (if id = 302 then some localCycle00302 else none))) else (if id < 304 then (if id = 303 then some localCycle00303 else none) else (if id < 305 then (if id = 304 then some localCycle00304 else none) else (if id = 305 then some localCycle00305 else none)))) else (if id < 309 then (if id < 307 then (if id = 306 then some localCycle00306 else none) else (if id < 308 then (if id = 307 then some localCycle00307 else none) else (if id = 308 then some localCycle00308 else none))) else (if id < 310 then (if id = 309 then some localCycle00309 else none) else (if id < 311 then (if id = 310 then some localCycle00310 else none) else (if id = 311 then some localCycle00311 else none))))))) else (if id < 334 then (if id < 323 then (if id < 317 then (if id < 314 then (if id < 313 then (if id = 312 then some localCycle00312 else none) else (if id = 313 then some localCycle00313 else none)) else (if id < 315 then (if id = 314 then some localCycle00314 else none) else (if id < 316 then (if id = 315 then some localCycle00315 else none) else (if id = 316 then some localCycle00316 else none)))) else (if id < 320 then (if id < 318 then (if id = 317 then some localCycle00317 else none) else (if id < 319 then (if id = 318 then some localCycle00318 else none) else (if id = 319 then some localCycle00319 else none))) else (if id < 321 then (if id = 320 then some localCycle00320 else none) else (if id < 322 then (if id = 321 then some localCycle00321 else none) else (if id = 322 then some localCycle00322 else none))))) else (if id < 328 then (if id < 325 then (if id < 324 then (if id = 323 then some localCycle00323 else none) else (if id = 324 then some localCycle00324 else none)) else (if id < 326 then (if id = 325 then some localCycle00325 else none) else (if id < 327 then (if id = 326 then some localCycle00326 else none) else (if id = 327 then some localCycle00327 else none)))) else (if id < 331 then (if id < 329 then (if id = 328 then some localCycle00328 else none) else (if id < 330 then (if id = 329 then some localCycle00329 else none) else (if id = 330 then some localCycle00330 else none))) else (if id < 332 then (if id = 331 then some localCycle00331 else none) else (if id < 333 then (if id = 332 then some localCycle00332 else none) else (if id = 333 then some localCycle00333 else none)))))) else (if id < 345 then (if id < 339 then (if id < 336 then (if id < 335 then (if id = 334 then some localCycle00334 else none) else (if id = 335 then some localCycle00335 else none)) else (if id < 337 then (if id = 336 then some localCycle00336 else none) else (if id < 338 then (if id = 337 then some localCycle00337 else none) else (if id = 338 then some localCycle00338 else none)))) else (if id < 342 then (if id < 340 then (if id = 339 then some localCycle00339 else none) else (if id < 341 then (if id = 340 then some localCycle00340 else none) else (if id = 341 then some localCycle00341 else none))) else (if id < 343 then (if id = 342 then some localCycle00342 else none) else (if id < 344 then (if id = 343 then some localCycle00343 else none) else (if id = 344 then some localCycle00344 else none))))) else (if id < 351 then (if id < 348 then (if id < 346 then (if id = 345 then some localCycle00345 else none) else (if id < 347 then (if id = 346 then some localCycle00346 else none) else (if id = 347 then some localCycle00347 else none))) else (if id < 349 then (if id = 348 then some localCycle00348 else none) else (if id < 350 then (if id = 349 then some localCycle00349 else none) else (if id = 350 then some localCycle00350 else none)))) else (if id < 354 then (if id < 352 then (if id = 351 then some localCycle00351 else none) else (if id < 353 then (if id = 352 then some localCycle00352 else none) else (if id = 353 then some localCycle00353 else none))) else (if id < 355 then (if id = 354 then some localCycle00354 else none) else (if id < 356 then (if id = 355 then some localCycle00355 else none) else (if id = 356 then some localCycle00356 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 5, 6, 4, 3, 2], ![5, 4, 3, 0, 6, 1], ![4, 5, 2, 0, 6, 1], ![3, 5, 2, 0, 6, 1], ![3, 4, 2, 0, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 90 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6016)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 5, 6, 4, 3, 2], ![5, 4, 3, 0, 6, 1], ![5, 4, 2, 0, 6, 1], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 51 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6017)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 6, 4, 3, 5, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 5], ![2, 0, 6, 1, 3, 4], ![0, 2, 5, 3, 4, 1]], proof := .tail 250 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6018)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 6, 4, 5, 3, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 0, 5, 6, 1], ![3, 2, 0, 6, 1, 5], ![2, 0, 3, 6, 1, 4], ![0, 2, 3, 5, 4, 1]], proof := .tail 94 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6019)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 6, 4, 5, 3, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 1, 5], ![2, 0, 6, 3, 1, 4], ![0, 2, 5, 3, 4, 1]], proof := .tail 140 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6020)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 0, 5, 6, 1], ![3, 2, 0, 5, 6, 1], ![2, 0, 3, 4, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 85 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6021)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 0, 5, 6, 1], ![3, 2, 0, 6, 5, 1], ![2, 0, 3, 6, 4, 1], ![0, 2, 3, 5, 4, 1]], proof := .tail 253 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6022)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 5, 1], ![2, 0, 6, 3, 4, 1], ![0, 2, 5, 3, 4, 1]], proof := .tail 100 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6023)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 6, 4, 5, 3, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 0, 6, 1, 5], ![2, 3, 0, 6, 1, 4], ![0, 2, 3, 5, 4, 1]], proof := .tail 288 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6024)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 0, 5, 6, 1], ![2, 3, 0, 4, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 231 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6025)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 0, 6, 5, 1], ![2, 3, 0, 6, 4, 1], ![0, 2, 3, 5, 4, 1]], proof := .tail 134 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6026)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 5, 0, 6, 1], ![2, 3, 4, 0, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 277 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6027)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 6, 4, 5, 3, 2], ![4, 5, 3, 0, 6, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 4], ![0, 2, 3, 5, 4, 1]], proof := .tail 247 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6028)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 6, 5, 4, 3, 2], ![4, 5, 3, 0, 6, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 0, 5, 6, 1], ![3, 2, 0, 4, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 188 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6029)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 6, 5, 4, 3, 2], ![4, 5, 3, 0, 6, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 4, 1], ![0, 2, 3, 5, 4, 1]], proof := .tail 186 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6030)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 6, 5, 4, 3, 2], ![4, 5, 3, 0, 6, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 5, 0, 6, 1], ![3, 2, 4, 0, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 264 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6031)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 6, 5, 4, 3, 2], ![5, 4, 3, 0, 6, 1], ![4, 5, 2, 0, 6, 1], ![3, 5, 2, 0, 6, 1], ![3, 4, 2, 0, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 64 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6032)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 6, 5, 4, 3, 2], ![5, 4, 3, 0, 6, 1], ![5, 4, 2, 0, 6, 1], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 308 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6033)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 4, 5, 6], ![2, 0, 1, 3, 5, 6], ![2, 0, 1, 3, 4, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 210 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6034)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 4, 5, 6], ![2, 0, 1, 3, 6, 5], ![2, 0, 1, 3, 6, 4], ![2, 0, 1, 3, 5, 4]], proof := .tail 131 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6035)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![2, 0, 1, 6, 3, 4], ![2, 0, 1, 5, 3, 4]], proof := .low (![34, 96, 160, 68, 52, 8, 119, 216, 349, 44, 238, 343, 136, 290, 304, 182, 153, 196, 233, 323, 167, 354, 35, 97, 97, 159, 112, 12]) }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6036)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 4, 6, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 1, 3, 4]], proof := .low (![225, 96, 160, 56, 219, 163, 119, 5, 307, 296, 39, 335, 136, 99, 72, 32, 335, 196, 259, 337, 335, 263, 124, 335, 135, 104, 207, 76]) }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6037)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 3, 4, 6, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 1, 3, 4]], proof := .low (![225, 96, 160, 56, 25, 115, 119, 5, 307, 296, 123, 157, 136, 99, 72, 32, 157, 196, 259, 337, 157, 263, 336, 157, 185, 239, 165, 294]) }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6038)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 3, 4, 6, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .low (![225, 96, 160, 56, 101, 176, 119, 5, 307, 296, 123, 201, 136, 99, 72, 32, 341, 196, 259, 337, 117, 285, 336, 21, 135, 342, 248, 177]) }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6039)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![2, 0, 1, 6, 3, 4], ![2, 0, 1, 5, 4, 3]], proof := .tail 133 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6040)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 4, 6, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 1, 4, 3]], proof := .tail 181 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6041)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 3, 4, 6, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 1, 4, 3]], proof := .tail 181 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6042)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 3, 4, 6, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 1, 4, 3]], proof := .tail 181 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6043)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 6, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 4, 1, 3]], proof := .tail 179 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6044)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 3, 6, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 4, 1, 3]], proof := .tail 179 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6045)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 3, 6, 4, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 4, 1, 3]], proof := .tail 179 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6046)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 3, 6, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 4, 5], ![2, 6, 0, 1, 3, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 4, 0, 1, 3]], proof := .tail 179 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6047)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 3, 6, 4, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 1, 6, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 4, 0, 1, 3]], proof := .tail 179 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6048)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 3, 6, 4, 5, 2], ![3, 6, 4, 5, 0, 1], ![2, 0, 1, 6, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 4, 2, 0, 1, 3]], proof := .tail 179 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6049)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 5, 4, 6], ![2, 0, 1, 5, 3, 6], ![2, 0, 1, 4, 3, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 268 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6050)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 5, 6, 4], ![2, 0, 1, 5, 6, 3], ![2, 0, 1, 4, 3, 6], ![2, 0, 1, 4, 3, 5]], proof := .low (![325, 258, 107, 132, 139, 8, 119, 184, 235, 80, 173, 212, 136, 209, 217, 1, 153, 327, 143, 289, 232, 232, 9, 244, 37, 159, 112, 12]) }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6051)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 5, 6, 3], ![2, 0, 1, 4, 6, 3], ![2, 0, 1, 4, 5, 3]], proof := .tail 312 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6052)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![2, 0, 1, 6, 4, 3], ![2, 0, 1, 5, 4, 3]], proof := .tail 313 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6053)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 4, 6, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![2, 0, 6, 1, 4, 3], ![2, 0, 5, 1, 4, 3]], proof := .low (![67, 122, 243, 318, 219, 163, 119, 316, 353, 114, 274, 335, 136, 81, 251, 48, 335, 348, 338, 50, 335, 204, 215, 335, 218, 104, 207, 76]) }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6054)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 3, 4, 6, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![2, 6, 0, 1, 4, 3], ![2, 5, 0, 1, 4, 3]], proof := .low (![67, 122, 243, 318, 187, 115, 119, 316, 353, 114, 303, 157, 136, 81, 251, 334, 157, 348, 338, 50, 157, 204, 215, 157, 218, 239, 154, 294]) }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6055)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 3, 4, 6, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 2, 0, 1, 4, 3]], proof := .low (![67, 122, 243, 318, 95, 176, 119, 316, 353, 114, 303, 201, 136, 81, 251, 46, 341, 348, 338, 50, 204, 204, 215, 21, 218, 342, 108, 177]) }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6056)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 6, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 1, 5, 3], ![2, 0, 6, 1, 4, 3], ![2, 0, 5, 4, 1, 3]], proof := .tail 36 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6057)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 3, 6, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 1, 5, 3], ![2, 6, 0, 1, 4, 3], ![2, 5, 0, 4, 1, 3]], proof := .tail 36 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6058)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 3, 6, 4, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 1, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 2, 0, 4, 1, 3]], proof := .tail 36 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6059)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 3, 6, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 6, 0, 1, 5, 3], ![2, 6, 0, 1, 4, 3], ![2, 5, 4, 0, 1, 3]], proof := .tail 30 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6060)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 3, 6, 4, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 6, 0, 1, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 2, 4, 0, 1, 3]], proof := .tail 30 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6061)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 3, 6, 4, 5, 2], ![3, 6, 4, 5, 0, 1], ![2, 0, 1, 6, 5, 4], ![6, 2, 0, 1, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 55 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6062)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 5, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 5, 4, 6], ![2, 0, 5, 1, 3, 6], ![2, 0, 4, 1, 3, 6], ![2, 0, 1, 3, 4, 5]], proof := .low (![355, 199, 198, 168, 4, 147, 119, 42, 27, 54, 138, 331, 136, 18, 282, 138, 7, 222, 195, 138, 146, 166, 297, 110, 345, 301, 287, 283]) }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6063)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 5, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 5, 6, 4], ![2, 0, 5, 1, 6, 3], ![2, 0, 4, 1, 3, 6], ![2, 0, 1, 4, 3, 5]], proof := .tail 190 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6064)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 5, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 5, 1, 6, 3], ![2, 0, 4, 1, 6, 3], ![2, 0, 1, 4, 5, 3]], proof := .tail 155 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6065)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 5, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 5, 6, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 1, 3, 6], ![2, 0, 4, 1, 3, 5]], proof := .low (![276, 326, 198, 98, 145, 78, 119, 223, 27, 174, 262, 83, 136, 3, 15, 295, 83, 292, 92, 183, 83, 103, 28, 118, 61, 339, 84, 298]) }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6066)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 5, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 1, 6, 3], ![2, 0, 4, 1, 5, 3]], proof := .low (![194, 214, 70, 286, 145, 78, 119, 309, 302, 344, 262, 83, 136, 257, 77, 295, 83, 63, 319, 142, 142, 142, 28, 118, 73, 339, 84, 298]) }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6067)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 6, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 6, 1, 3], ![2, 0, 4, 5, 1, 3]], proof := .tail 266 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6068)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 6, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 5, 1, 3], ![2, 0, 6, 4, 1, 3], ![2, 0, 5, 4, 1, 3]], proof := .tail 22 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6069)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 3, 6, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 5, 1, 3], ![2, 6, 0, 4, 1, 3], ![2, 5, 0, 4, 1, 3]], proof := .tail 93 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6070)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 3, 6, 5, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 5, 1, 3], ![6, 2, 0, 4, 1, 3], ![5, 2, 0, 4, 1, 3]], proof := .low (![220, 241, 240, 180, 278, 162, 119, 305, 189, 156, 106, 111, 300, 113, 261, 169, 111, 333, 211, 260, 111, 322, 246, 191, 137, 120, 47, 205]) }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6071)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 3, 6, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 6, 0, 5, 1, 3], ![2, 6, 0, 4, 1, 3], ![2, 5, 4, 0, 1, 3]], proof := .tail 227 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6072)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 3, 6, 5, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 6, 0, 5, 1, 3], ![6, 2, 0, 4, 1, 3], ![5, 2, 4, 0, 1, 3]], proof := .tail 227 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6073)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 3, 6, 5, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 0, 1, 6, 5, 4], ![6, 2, 0, 5, 1, 3], ![6, 2, 0, 4, 1, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 130 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6074)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 3, 5, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 5, 4, 6], ![2, 5, 0, 1, 3, 6], ![2, 4, 0, 1, 3, 6], ![2, 0, 1, 3, 4, 5]], proof := .low (![69, 199, 198, 237, 192, 26, 119, 42, 27, 224, 6, 125, 136, 18, 230, 6, 151, 222, 195, 6, 146, 166, 127, 306, 291, 40, 16, 267]) }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6075)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 3, 5, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 5, 6, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 0, 1, 3, 6], ![2, 0, 1, 4, 3, 5]], proof := .tail 121 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6076)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 3, 5, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 0, 1, 6, 3], ![2, 0, 1, 4, 5, 3]], proof := .tail 350 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6077)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 3, 5, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 5, 6, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 1, 3, 6], ![2, 0, 4, 1, 3, 5]], proof := .tail 280 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6078)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 3, 5, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 1, 6, 3], ![2, 0, 4, 1, 5, 3]], proof := .tail 280 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6079)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 3, 6, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 6, 1, 3], ![2, 0, 4, 5, 1, 3]], proof := .tail 275 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6080)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 3, 5, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 5, 6, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 0, 1, 3, 6], ![2, 4, 0, 1, 3, 5]], proof := .low (![276, 326, 198, 170, 178, 82, 119, 223, 27, 174, 53, 228, 136, 3, 15, 295, 228, 252, 92, 183, 228, 103, 75, 236, 158, 351, 252, 320]) }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6081)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 3, 5, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 0, 1, 6, 3], ![2, 4, 0, 1, 5, 3]], proof := .low (![293, 214, 70, 286, 178, 82, 119, 309, 302, 344, 53, 228, 136, 257, 77, 295, 228, 63, 319, 142, 142, 142, 75, 236, 158, 351, 252, 320]) }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6082)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 3, 6, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 0, 6, 1, 3], ![2, 4, 0, 5, 1, 3]], proof := .tail 266 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6083)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 6, 0, 1, 3], ![2, 4, 5, 0, 1, 3]], proof := .tail 29 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6084)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 6, 5, 0, 1, 3], ![2, 6, 4, 0, 1, 3], ![2, 5, 4, 0, 1, 3]], proof := .tail 356 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6085)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 6, 5, 0, 1, 3], ![6, 2, 4, 0, 1, 3], ![5, 2, 4, 0, 1, 3]], proof := .low (![220, 241, 240, 149, 213, 208, 119, 305, 189, 156, 175, 13, 136, 113, 261, 169, 13, 310, 211, 260, 13, 322, 60, 299, 152, 279, 71, 332]) }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6086)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 0, 1, 6, 5, 4], ![6, 2, 5, 0, 1, 3], ![6, 2, 4, 0, 1, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 346 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6087)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 3, 5, 4, 6, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 1, 5, 4, 6], ![5, 2, 0, 1, 3, 6], ![4, 2, 0, 1, 3, 6], ![2, 0, 1, 3, 4, 5]], proof := .low (![69, 199, 198, 31, 74, 234, 119, 42, 27, 224, 273, 317, 136, 18, 230, 272, 153, 222, 195, 265, 146, 166, 352, 324, 193, 229, 116, 172]) }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6088)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 3, 5, 4, 6, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 1, 5, 6, 4], ![5, 2, 0, 1, 6, 3], ![4, 2, 0, 1, 3, 6], ![2, 0, 1, 4, 3, 5]], proof := .tail 314 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6089)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 3, 5, 4, 6, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![5, 2, 0, 1, 6, 3], ![4, 2, 0, 1, 6, 3], ![2, 0, 1, 4, 5, 3]], proof := .tail 23 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6090)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 3, 5, 6, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 1, 5, 6, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 1, 3, 6], ![2, 0, 4, 1, 3, 5]], proof := .tail 311 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6091)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 3, 5, 6, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 1, 6, 3], ![2, 0, 4, 1, 5, 3]], proof := .tail 58 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6092)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 3, 6, 5, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 6, 1, 3], ![2, 0, 4, 5, 1, 3]], proof := .tail 65 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6093)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 3, 5, 6, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 1, 5, 6, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 0, 1, 3, 6], ![2, 4, 0, 1, 3, 5]], proof := .tail 148 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6094)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 3, 5, 6, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 0, 1, 6, 3], ![2, 4, 0, 1, 5, 3]], proof := .tail 58 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6095)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 3, 6, 5, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 0, 6, 1, 3], ![2, 4, 0, 5, 1, 3]], proof := .tail 65 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6096)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 6, 0, 1, 3], ![2, 4, 5, 0, 1, 3]], proof := .tail 271 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6097)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 3, 5, 6, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 0, 1, 5, 6, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 0, 1, 3, 6], ![4, 2, 0, 1, 3, 5]], proof := .low (![276, 326, 198, 329, 2, 245, 119, 223, 27, 174, 53, 14, 136, 3, 15, 295, 347, 226, 92, 183, 45, 103, 249, 0, 256, 203, 284, 281]) }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6098)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 3, 5, 6, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 0, 1, 6, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 0, 1, 6, 3], ![4, 2, 0, 1, 5, 3]], proof := .low (![293, 214, 70, 286, 2, 245, 119, 309, 302, 344, 53, 14, 136, 257, 77, 295, 347, 10, 319, 142, 142, 142, 144, 0, 270, 203, 284, 281]) }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6099)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 3, 6, 5, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 0, 1, 6, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 0, 6, 1, 3], ![4, 2, 0, 5, 1, 3]], proof := .low (![220, 241, 240, 43, 88, 102, 119, 305, 189, 11, 330, 33, 242, 113, 261, 330, 33, 89, 211, 330, 33, 322, 206, 24, 129, 109, 161, 321]) }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6100)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 0, 1, 6, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 6, 0, 1, 3], ![4, 2, 5, 0, 1, 3]], proof := .low (![220, 241, 240, 86, 41, 128, 119, 305, 189, 156, 105, 315, 136, 113, 261, 105, 315, 87, 211, 105, 315, 87, 141, 19, 87, 17, 91, 221]) }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6101)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 0, 1, 6, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 6, 2, 0, 1, 3], ![4, 5, 2, 0, 1, 3]], proof := .tail 340 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6102)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 0, 1, 6, 5, 4], ![6, 5, 2, 0, 1, 3], ![6, 4, 2, 0, 1, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 164 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6103)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 4, 5], ![2, 0, 6, 1, 3, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 4, 3, 1]], proof := .tail 254 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6104)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 3], ![2, 0, 6, 1, 4, 3], ![2, 0, 5, 4, 3, 1]], proof := .tail 36 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6105)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 6, 1, 3], ![2, 0, 4, 5, 3, 1]], proof := .tail 202 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6106)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 5, 1, 3], ![2, 0, 6, 4, 1, 3], ![2, 0, 5, 4, 3, 1]], proof := .tail 79 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6107)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 6, 1, 3], ![2, 0, 4, 5, 3, 1]], proof := .tail 66 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6108)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 6, 3, 5, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 6, 1, 3], ![2, 0, 4, 5, 3, 1]], proof := .tail 269 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6109)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 4, 5], ![2, 0, 6, 1, 3, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 4, 3, 1]], proof := .tail 20 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6110)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 3], ![2, 6, 0, 1, 4, 3], ![2, 5, 0, 4, 3, 1]], proof := .tail 36 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6111)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 5, 1, 3], ![2, 6, 0, 4, 1, 3], ![2, 5, 0, 4, 3, 1]], proof := .tail 150 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6112)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 1, 4, 5], ![2, 0, 6, 1, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 4, 3, 1]], proof := .tail 126 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6113)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 2, 0, 4, 3, 1]], proof := .tail 36 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6114)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 5, 1, 3], ![6, 2, 0, 4, 1, 3], ![5, 2, 0, 4, 3, 1]], proof := .tail 59 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6115)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 0, 6, 1, 3], ![2, 4, 0, 5, 3, 1]], proof := .tail 202 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6116)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 0, 6, 1, 3], ![2, 4, 0, 5, 3, 1]], proof := .tail 269 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6117)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 0, 6, 1, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 0, 6, 1, 3], ![4, 2, 0, 5, 3, 1]], proof := .tail 202 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6118)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 4, 5], ![2, 6, 0, 1, 3, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 4, 0, 3, 1]], proof := .tail 20 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6119)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 6, 0, 1, 5, 3], ![2, 6, 0, 1, 4, 3], ![2, 5, 4, 0, 3, 1]], proof := .tail 30 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6120)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 6, 0, 5, 1, 3], ![2, 6, 0, 4, 1, 3], ![2, 5, 4, 0, 3, 1]], proof := .tail 227 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6121)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 6, 0, 1, 3], ![2, 4, 5, 0, 3, 1]], proof := .tail 255 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6122)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 6, 5, 0, 1, 3], ![2, 6, 4, 0, 1, 3], ![2, 5, 4, 0, 3, 1]], proof := .tail 356 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6123)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 6, 0, 1, 3], ![2, 4, 5, 0, 3, 1]], proof := .tail 269 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6124)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 1, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 4, 0, 3, 1]], proof := .tail 20 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6125)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 6, 0, 1, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 2, 4, 0, 3, 1]], proof := .tail 30 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6126)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 6, 0, 5, 1, 3], ![6, 2, 0, 4, 1, 3], ![5, 2, 4, 0, 3, 1]], proof := .tail 227 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6127)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 6, 5, 0, 1, 3], ![6, 2, 4, 0, 1, 3], ![5, 2, 4, 0, 3, 1]], proof := .tail 59 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6128)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 0, 6, 1, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 6, 0, 1, 3], ![4, 2, 5, 0, 3, 1]], proof := .tail 202 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6129)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 6, 4, 5, 0, 1], ![2, 0, 6, 1, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 4, 2, 0, 3, 1]], proof := .tail 171 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6130)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 6, 4, 5, 0, 1], ![2, 0, 6, 1, 5, 4], ![6, 2, 0, 1, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 4, 2, 0, 3, 1]], proof := .tail 57 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6131)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 3, 5, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 0, 6, 1, 5, 4], ![6, 2, 0, 5, 1, 3], ![6, 2, 0, 4, 1, 3], ![5, 4, 2, 0, 3, 1]], proof := .tail 130 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6132)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 0, 6, 1, 5, 4], ![6, 2, 5, 0, 1, 3], ![6, 2, 4, 0, 1, 3], ![5, 4, 2, 0, 3, 1]], proof := .tail 346 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6133)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 0, 6, 1, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 6, 2, 0, 1, 3], ![4, 5, 2, 0, 3, 1]], proof := .tail 62 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6134)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 0, 6, 1, 5, 4], ![6, 5, 2, 0, 1, 3], ![6, 4, 2, 0, 1, 3], ![5, 4, 2, 0, 3, 1]], proof := .tail 38 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6135)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 0, 1, 4, 5], ![2, 6, 0, 1, 3, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 4, 3, 0, 1]], proof := .tail 49 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6136)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 0, 1, 5, 4], ![2, 6, 0, 1, 5, 3], ![2, 6, 0, 1, 4, 3], ![2, 5, 4, 3, 0, 1]], proof := .tail 30 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6137)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 0, 1, 5, 4], ![2, 6, 0, 5, 1, 3], ![2, 6, 0, 4, 1, 3], ![2, 5, 4, 3, 0, 1]], proof := .tail 227 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6138)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 0, 1, 5, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 6, 0, 1, 3], ![2, 4, 5, 3, 0, 1]], proof := .tail 197 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6139)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 0, 1, 5, 4], ![2, 6, 5, 0, 1, 3], ![2, 6, 4, 0, 1, 3], ![2, 5, 4, 3, 0, 1]], proof := .tail 356 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6140)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 6, 0, 1, 5, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 6, 0, 1, 3], ![2, 4, 5, 3, 0, 1]], proof := .tail 328 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6141)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 0, 1, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 4, 3, 0, 1]], proof := .tail 200 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6142)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 0, 1, 5, 4], ![2, 6, 0, 1, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 2, 4, 3, 0, 1]], proof := .tail 30 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6143)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (6016 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 6016 ≤ id.val) (hhigh : id.val < 6144) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 6016)) = true := by
  let j : Fin 128 := ⟨id.val - 6016, by omega⟩
  have hsum : 6016 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (6016 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard047
