import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard164
open N4R2OuterLeftReplay

-- Cycle fingerprint 01150ce22ee5b1aa11912cab812a97f4175f53252dd5f7066f45557a32abc933.
def localCycle00000 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 021ac35a6ddb46f8d291d4bba33d8306e2191b6137179b18e9e0f35d40d19528.
def localCycle00001 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .distance 2 5]
    constant := ![-1, -1, -1, -1, 0, -1, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 23 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .gapLower 2 6]

-- Cycle fingerprint 0277d85dcb7ccaf8fbc2ecc05f060c19d8342a830e47a26a875b5e083caff50c.
def localCycle00002 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 1 6]
    constant := ![-2, -2, -1, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .triangle 3 0, .triangle 17 1, .triangle 18 2]

-- Cycle fingerprint 03ab1a208e0817c26de9e0b348cfb132a6722065e1559bd2c27e842471bdf04b.
def localCycle00003 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 4]
    constant := ![-2, -2, 3, -1, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .triangle 17 1, .triangle 18 2, .triangle 23 1]

-- Cycle fingerprint 04683467d74f776cd1535a31bdae98ea666415c6738cd5118d8ea42c63cd77c9.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 1 6, .distance 1 5, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6]
    constant := ![2, 0, 0, 0, -3, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, true, false, false, false, false] }
  origin := ![.gapUpper 6 0, .triangle 24 1, .triangle 17 1, .triangle 16 2, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint 05443c62995ba9d30c10ea71dbeb44508ee9df970fa238efe16b49c9f6c97aae.
def localCycle00005 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 0 1, .triangle 16 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 05a6ab389df82b3ae612c0c4b108f5f752bb0d65cc7b7143961cb25ad4d7ebb6.
def localCycle00006 : Cycle where
  length := 13
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 05c251124d58d17adfd37a32b6c12b01ee66b07b6e5653d15b727e43f099cd32.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 17 1, .triangle 16 2, .triangle 23 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 05fd974f38f141718d07110e9a78df658018cf5dce18c601ed5ba184c02e82b4.
def localCycle00008 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 1034e78a9c9f2ab5180c7223a0a7d97482f7d69aa438630b26485cc6cf3f83af.
def localCycle00009 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 4, .theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1, .triangle 4 0, .gapLower 1 4, .triangle 17 1]

-- Cycle fingerprint 124fb9cba7b65d44694e335ec1392ef04dfdd938e2d5abbf025e52c0c78fa062.
def localCycle00010 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint 13b36f4a2ce8197911b70aa3fc915779a255122a8c6e4bc8cde4a945877636db.
def localCycle00011 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 17 1, .triangle 18 0, .triangle 27 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 15421eb6635bfa386ee74987b9f23f15f2e5f76449c5b34ca19994d66d1d865d.
def localCycle00012 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6, .distance 1 6]
    constant := ![-2, 0, 0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 22 1, .triangle 19 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint 1546a9a38150f9a763cda117ff804c922898917a226ba06532d6037d68eb6bb6.
def localCycle00013 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .gapLower 4 0]

-- Cycle fingerprint 18e29c27f9ae3e39c24d6922278e2fca2f503062b250ca3f6979e8b42c84cc2a.
def localCycle00014 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 18f9d5de9e69591ed4b9a483927a423d64751b8119d8d5b895447b41baf69494.
def localCycle00015 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 6, .triangle 3 0, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 195be1b48aa6290b889b664d65a2459be4f142f6536b3f7ef7e12d0a8923af58.
def localCycle00016 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 5, .corridorUpper 0 1]

-- Cycle fingerprint 1b09a3270b1c240ebfe9219642b0f0f310b3beb290020fc7a839629d609f8463.
def localCycle00017 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 24 1, .corridorLower 5 6]

-- Cycle fingerprint 1b0ffa8fdfc43cdd8996de571e400e53bd7da86a9c289ff0bc7198e6d02c216c.
def localCycle00018 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 1 3]
    constant := ![-3, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 19 0]

-- Cycle fingerprint 1b7549f6c95cd062a976b2544e174d539b550277c12cf67c50047385615323c5.
def localCycle00019 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 1 6, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 17 1, .gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 1bc36af1aa58ff570b5760ec6ca2b7adb16c4fa0149f1f09ea16f9be405bf896.
def localCycle00020 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 2]
    constant := ![-1, 0, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, true] }
  origin := ![.triangle 16 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .gapUpper 5 1, .triangle 17 1]

-- Cycle fingerprint 21fbb6e70d1888583bd6c25592a643e772e273684d4ae35bcdbccdf8e5554c5f.
def localCycle00021 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6]
    constant := ![-2, 0, 0, -2, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 16 2, .triangle 19 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2]

-- Cycle fingerprint 225f918da7fb4e9996a01d4131932a3507bc11df0f7e4f5d27577d560ea0b2db.
def localCycle00022 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 24 1, .gapLower 1 3, .corridorLower 1 2, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint 2420ff2f3a1aac6f504efabd611f61a7a1cdd82eae05309973892227e6da1c5c.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6, .distance 1 6]
    constant := ![0, 0, 0, 0, -3, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, true, false, false, false, true] }
  origin := ![.triangle 24 1, .triangle 17 1, .triangle 16 2, .triangle 19 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint 2526a229cf707470781d74d48e39d0da716fd5c5c1629759077cf3faf07fc412.
def localCycle00024 : Cycle where
  length := 3
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .theta 1]
    constant := ![3, -3, -1]
    coefficient := ![1, 0, 0]
    strict := ![false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 1 5, .corridorLower 1 5]

-- Cycle fingerprint 2644978e9674ce9b055f3d692c1325f9a8f3ee0a7b49b58f0e1ee05bde8204f7.
def localCycle00025 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3]
    constant := ![-1, 0, 0, 3, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .triangle 16 0, .triangle 25 1]

-- Cycle fingerprint 268ee9727c60a2c02e54e4b3b6f350f09aa3d993a51841d17175600ffa95cc2a.
def localCycle00026 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 0, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint 27dc8fe2611f2a75e72a4596884e0984709e7014ccd60c75fb6879010a35390d.
def localCycle00027 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 1 2, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 0 1, .triangle 16 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 2a97442395a219b837f67b033f670f6831df2473eafc1e61aef2ef92c6a5ce33.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .gapLower 3 0]

-- Cycle fingerprint 2a977c96141908bf3990635620d25be5248d8d787cbad3e94451af5012c0c6e5.
def localCycle00029 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 2de08b56557a560f36d8dd379d3ef6d6462097e114567a076655b56ff99ddf0a.
def localCycle00030 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 6, .theta 1, .distance 0 1, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 6, .corridorUpper 0 1, .gapLower 1 5, .triangle 17 1]

-- Cycle fingerprint 2f68b6a7e1ca84ef22ad536f2c8ecd666c06f92001053aaa27f7d80179f6129b.
def localCycle00031 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 7 0, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 2f9194b75fdb2360005f594c94cb837076f27ef861298a0c9fa595f0402ffd13.
def localCycle00032 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 30987bb0d4285eca26e555f8641ffc5c81a6dd750658fc497c38c6a57b48b569.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-1, 0, -1, 0, 2, -1, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 4 0, .triangle 24 1, .gapLower 1 3]

-- Cycle fingerprint 323ff1a5fb20fb69a38b93e12d029a52fe35a181d12f3208d418cb3686207fcb.
def localCycle00034 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 1 6]
    constant := ![-2, 0, -2, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 19 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .triangle 17 1, .triangle 18 2]

-- Cycle fingerprint 336ceedae5ba5e2bbfd36bbe82c284bc0f24b3735024ff6a926b3ca48168cb66.
def localCycle00035 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -1, 0, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.gapLower 1 5, .triangle 18 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1]

-- Cycle fingerprint 353610c231873a41edd1032edbc36d21a4a09dfdaf922f85429ad6c32e734689.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 16 2, .gapLower 4 0]

-- Cycle fingerprint 35852259b9048106db03d609710b65c132852154ecb42e04a4252e22ff13edc8.
def localCycle00037 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .gapLower 5 3, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 37bd001a40f86cd079db89426caeea10e02bee6e6dbd9bc30bf9642cccfa1e2a.
def localCycle00038 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 1 4, .distance 1 3]
    constant := ![-2, 3, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .triangle 17 1, .gapLower 1 2, .triangle 19 1]

-- Cycle fingerprint 38d8edd14eae1ad97af3c65f95e6207bf5628f0ac29b90f3f6b6d3b4322fbf86.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 30 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 3bd1dc9750982b9ead6bb9dee0356d18478aa52b59b1d4d12d1a54dd6e77cd3e.
def localCycle00040 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-1, 3, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 402bf5753520684ac3ce84743bf2371e47d6d0b07150ac42ecdb9100af9cc34b.
def localCycle00041 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 41391de3af3fbf1d874ae758c83f0ab1cec8e4c700e0ae582fb0c45bde080d53.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 8 0, .triangle 18 0, .triangle 16 0, .gapLower 4 0]

-- Cycle fingerprint 45185afb7c150cf833a8a1250cc801b4f5180d07d605c5ec5802b4bbbccc35ea.
def localCycle00043 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 2]
    constant := ![0, -2, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 18 2, .gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 17 1]

-- Cycle fingerprint 4694c18d372ee9a8368c24e073cad50beffb510bf01e6ea86b2e7d35d510c5c4.
def localCycle00044 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 1 4, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5]
    constant := ![-2, -2, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .corridorLower 1 4, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 24 1]

-- Cycle fingerprint 46d2ab022766b55531df1b3ca15c672e485f5bbcdc24ec6c416be0cb2b8712d5.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 23 1, .triangle 29 2, .triangle 30 1, .corridorLower 5 6]

-- Cycle fingerprint 4745240325930cc97fbc7e7c467a499ec4e4df61e4872af8bcf573a657037dda.
def localCycle00046 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1]
    constant := ![3, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .triangle 24 1, .gapLower 1 3, .corridorLower 1 2]

-- Cycle fingerprint 47b8530fd21aab860d4ed48056ff37c7b690e12492a1025d68ad03504eaba447.
def localCycle00047 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 18 0, .triangle 30 1, .gapUpper 5 1]

-- Cycle fingerprint 499da1f7ecf2bdfa2b25b8b15a031c515ef94a3986898c20493b22cf2e98fc9c.
def localCycle00048 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 1 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 16 2, .gapLower 4 0]

-- Cycle fingerprint 4ad1bbe2cdf688e2d68e176e9758483e24bc25c51bd3b1c379727b1d0660e376.
def localCycle00049 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 3, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .gapLower 3 0]

-- Cycle fingerprint 4b709bd21cb71efeb66d4ae3a11949f85b955b14e480b4d3a19f5b60f5c4e400.
def localCycle00050 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 2, .triangle 7 0, .triangle 0 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 4f0373d2b03d49ead0182153158bdc6f7598cd47afcfef4eb9f1854d24323df2.
def localCycle00051 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 4f36f3222eb6c9b1847dd5a52b93fca91461fb8e8017d27006632d7a8bdbdc90.
def localCycle00052 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 529c01a041236c995e6a5c12e152c759288e1307ef4338f5216550c8c5a60e4c.
def localCycle00053 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 54722a95e48c2e0c36abfbe3b72c927d9dd30fe8a1a3329eaf83f4979b070c96.
def localCycle00054 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 54cacf0e7cc1d0fbb07e497dadec0312232aaed26fbef66feceec7e84b29bfb8.
def localCycle00055 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6, .distance 1 6]
    constant := ![-2, 0, -2, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 22 1, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint 55634df2cda92b5e64c0bc9e5266c42b7bb396a9b0ccd2367678e9900b05fc25.
def localCycle00056 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 588a1130cec0b8a7f92041e674778653fa8fa50f3d42ac7cffd6cb51a77c86ed.
def localCycle00057 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-1, 3, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .corridorUpper 0 1, .triangle 4 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 5c11f8efd9933e863b76679935b5dd348610ae46f3f2055668fa1f7b89d0c1f6.
def localCycle00058 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6]
    constant := ![-2, 0, -2, -1, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 16 2, .gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2]

-- Cycle fingerprint 5c97931c8f848bfd8dcdd3cd46aa13f816ab4f60ff49923d12d48e2815c13cbf.
def localCycle00059 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 3, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 5d7889e23a0a48a3eb7dbe0f757d4bf94ce3fc3bdb5e4099ad206482e7d16d81.
def localCycle00060 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 2, .triangle 8 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 5e9eb525a8d6043c32a8e9a26b2f8e4daa38dab29d3b51c9b9bf7ec645a26fb6.
def localCycle00061 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![0, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 17 1, .triangle 16 2, .triangle 19 1, .gapLower 1 0, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 6019e15f1886865fd8a8b8a9327c8887661adf3578a8458cc6daa7f0bd97fb03.
def localCycle00062 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 609d6c12915b51fa21682aa14a51ccff8a62aab0acc979958b2f6334b47e5cd1.
def localCycle00063 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![0, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 24 1, .triangle 17 1, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint 615f5da8df8c181ca727c104bb428a23ddff37723bb8b159a9b50e46c1698071.
def localCycle00064 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 4]
    constant := ![-3, -1, 3, -1, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .triangle 3 0, .triangle 17 1, .triangle 18 2, .triangle 23 1]

-- Cycle fingerprint 62fa7fb08bc47695e9d4316acd127426b95ecea6d3d0a8878c5651e15e4465e6.
def localCycle00065 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 63d0041e983d982c5d9e63ac9735cf74d22ae6384145af5dac4147368c5bb571.
def localCycle00066 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![2, -1, 0, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .triangle 24 1, .triangle 17 1, .triangle 16 2, .triangle 19 1, .gapLower 1 0]

-- Cycle fingerprint 666e3d839e04291db6baec1c19afbe78d58e9027fed79153c00fb48ba8f3bef3.
def localCycle00067 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 66f74364898fe96142b9b910432091d9f2b89461c60840d2cd6320b2794dfb29.
def localCycle00068 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 68149d5b3ec9f39230dfc67d72c054d71c1f4b0af9ebd57f0ed3a794f347d133.
def localCycle00069 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -1, 0, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.gapLower 1 5, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1]

-- Cycle fingerprint 687d500af29364a557624eb69a20ab846bd2bae8cbe2afec5769a9709fe22fb1.
def localCycle00070 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .gapLower 4 0]

-- Cycle fingerprint 6bb1de78ba5600a34fdf6893cd9640df72c13d64c997548ac9b1a60b6c7d03ad.
def localCycle00071 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, -1, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 17 1, .triangle 16 2, .gapLower 1 1, .corridorLower 1 3]

-- Cycle fingerprint 6c44b8a2bf7a65a2a41c53f8d6835bbbfca096fc3d78b87c409b8038ecb33c47.
def localCycle00072 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 18 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 6cf325d2ffac91f4f8657f955dac4e20495dca2545387d2068f5735596f99de7.
def localCycle00073 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 4, .theta 1, .distance 0 1, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 18 1]

-- Cycle fingerprint 6db6a5c6d8cbc65b8c8d9363d5d7bab5759b2eceecf91c1cdeeb28c0cfe45cb3.
def localCycle00074 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 2]
    constant := ![-1, 0, -1, 0, 0, 3, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint 6ece90415e29f69367f8a4d3f2dd35d5a5df900a74275a9a39e7614ae01f36c9.
def localCycle00075 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 31 0, .triangle 34 0, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 16 0, .triangle 15 0, .gapLower 3 0]

-- Cycle fingerprint 6fcf29d9864c5eff0379dca8d0d7bb762b87449f138ee9b278535e840ca26ec9.
def localCycle00076 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-1, 0, -1, 0, 1, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 4 0, .triangle 24 1, .triangle 17 1]

-- Cycle fingerprint 7136ffa102ae8dc7252a543779e95e0767aa287f3056541ad97f0e7b8658446d.
def localCycle00077 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Cycle fingerprint 7259d913abf72cf39e13ef91f091ddc0e73ba3cfbd4c0a36d2bd31fc9ebc02a4.
def localCycle00078 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 1, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 72cb9bccca5fec530bcea9c180d6ec67e77f64e914c51c2b64a0bcfd8eb9691e.
def localCycle00079 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .corridorLower 4 6]

-- Cycle fingerprint 73bcd225a092d29be6619b2991fd633b79cc2330c5763eddfd66375b56beb66c.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4]
    constant := ![0, -1, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true, false, false] }
  origin := ![.triangle 25 1, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 2, .gapLower 1 3, .triangle 16 0]

-- Cycle fingerprint 74e474b6f031b140b7703fd9aa6facfd01ec64f001f20877413362ad87a0311f.
def localCycle00081 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 75cd5d42b3ad260a86d5f41f1347789dd25873450cb72c22f57e98b1ba11c8e9.
def localCycle00082 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 2, 0, -2, 0, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .gapLower 1 3, .triangle 16 2, .triangle 19 1, .gapLower 1 0]

-- Cycle fingerprint 768cd24c1446f4e247f4c4717e1a8a7a1088a86a7d056c604a0ef77f83cbe0f3.
def localCycle00083 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 77bb6618699b53b95d6fb8848a7d7aabd3882944554b6f817a79c48ced80ca6d.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-1, 0, -1, 0, 2, -1, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 3 0, .triangle 24 2, .gapLower 1 3]

-- Cycle fingerprint 7d16f12f40c41fa3a7b06d47771a59717e5cb8723778621511c7e604a756354d.
def localCycle00085 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, 0, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 17 1, .triangle 18 2, .triangle 23 1, .gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1]

-- Cycle fingerprint 7eee1c132e90d3f786ec8421586c755a8d70ef1563a3c34124c4ef0ad28def4b.
def localCycle00086 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 2, .triangle 13 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Cycle fingerprint 7f79a790d02e6378ee6b6d387895973755dd19b303423cea0a7708f0c47995b4.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 31 0, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .gapLower 3 0]

-- Cycle fingerprint 8095afb2d6432dd0a995b1aca3c6db25ca0bd52acc5308b5f7257dd766e933e4.
def localCycle00088 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 16 2, .triangle 23 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 80a7976cd090a254d5fd9642082c58933985bad57c6263f057b3fab02fcef0a7.
def localCycle00089 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .theta 1]
    constant := ![0, 0, 2, -3, -1]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .corridorLower 1 5]

-- Cycle fingerprint 81c99a0099e8b45b5abc51df9ded052a562387bf93886ff884c4bc3b632a0746.
def localCycle00090 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 20 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 828c745619b3e572fa7e5bf4b507da82c00b83a5f4442df015f4b59998715186.
def localCycle00091 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .triangle 17 1, .gapLower 1 2, .triangle 19 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 82d9225f986c9e2a9003c7aef6cd835db4d12839d9a0a350f37ce05041d811aa.
def localCycle00092 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 8553b601074bc69fe6906aa30291c8b1eae3b43a44b035dbf5d3b95fcf02d2cc.
def localCycle00093 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 2, .theta 1]
    constant := ![3, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 1 3, .corridorLower 1 2]

-- Cycle fingerprint 8641ba6f8cc8c8b39f8cbc03c1091d0206d7e052790d33206262bf356ff24322.
def localCycle00094 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 868b1be11ca825773aad590bac731f0c50a009a720dfbf38214da68ed262ca12.
def localCycle00095 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-2, 3, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .triangle 17 1, .gapLower 1 3, .triangle 21 1]

-- Cycle fingerprint 86f603d6dc603a38f7d28f63b8fd3bd10109f6f22b7c70e50f14a9d8ec725f4d.
def localCycle00096 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![2, -1, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .triangle 17 1, .triangle 18 2, .gapLower 1 2, .triangle 19 1, .corridorLower 1 3]

-- Cycle fingerprint 8745afb41611656a59f1e90a7cabc3a4c61a643f77ca8921cd39c60162753d25.
def localCycle00097 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 29 1, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Cycle fingerprint 8880090a011db507eaa7f4b1fbcfe3f90d63838000df9de17736a75c88400865.
def localCycle00098 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .gapLower 1 4, .corridorLower 1 5]

-- Cycle fingerprint 88cec0eca9981f56587ec3aafc19e25f024317afc608acefb35e17828a5c996a.
def localCycle00099 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 0 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 8ac4aa43cd7f557a1a174236de144fc6fc3a4ee01a8c9ee84bfbed6c1cb229a5.
def localCycle00100 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 17 1, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 8b0d811a5ab06b08164ca73dd96a2d3dcd266de448ba987535ac5eed607661c7.
def localCycle00101 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 8cd2e38d486a1dd160e03bcc6f4e89fc194f2bbdcd49012c175f629e66c83b70.
def localCycle00102 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 4, .theta 1]
    constant := ![3, -1, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 17 1, .triangle 18 2, .gapLower 1 2, .corridorLower 1 4]

-- Cycle fingerprint 8f2493ae2483afffc1bf6cc698cd18b768fbd89fee3d64f2ff2aebf1098d5ebe.
def localCycle00103 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 91279a7295343ec0c4039b131f1c31de9c2cedb42aec97ccff2babb495ef1ab1.
def localCycle00104 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 16 0, .gapLower 4 0]

-- Cycle fingerprint 93e2dc405d0855dda8542ff105d2af3de7da4ac7ee7e12ff14bf1c24f120492b.
def localCycle00105 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .triangle 7 0, .triangle 0 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 981fbe61b5a063a5baa57a2880f47b998c0e6f3832afc007779c277d3e411189.
def localCycle00106 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 9863981362768781745449989498454f67f067abf06be568844e887254a8cc78.
def localCycle00107 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 19 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 9a4241f2435eab4a8ea46b33c17f0c3cb07e95d62c5af254d7a579dcbe674209.
def localCycle00108 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-1, 0, 0, 0, -3, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false] }
  origin := ![.triangle 3 0, .triangle 17 1, .triangle 16 2, .triangle 19 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 9f3ec60a32ba1fe399778468409629e658bcde32ae7a41c96cd7e2e42d436bcc.
def localCycle00109 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true] }
  origin := ![.triangle 30 1, .gapUpper 5 1, .triangle 17 1, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint a4e8a3fcc72c87d7ae064c6ee0556d718af758c893492126a971896a264f5ef9.
def localCycle00110 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint a6eb1ad6fcf2c5777966a42ad35c99e0d63689ccf0327727f90a6f4888f097df.
def localCycle00111 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 22 1]

-- Cycle fingerprint a7e9e7f0cfdc016d4d342d7ffa6dfd7f0c1ba54f232b83fe63f11d5f06441f2c.
def localCycle00112 : Cycle where
  length := 14
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6]
    constant := ![-1, 0, 0, -1, -1, 0, 0, 3, -1, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 24 0, .gapLower 1 3, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 34 1]

-- Cycle fingerprint a8132677017dee14a0cce9bf20d4d9ecc03884c57aa02d339f55bfae6ebf793d.
def localCycle00113 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![0, -1, -1, 4, -1, -1, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .gapLower 2 6, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint ac3072fe7349fb8782c8e59df8eb919a94db53975b821a2dddb50bd6eb4a344f.
def localCycle00114 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 6, .triangle 3 0, .triangle 17 1, .triangle 18 0, .triangle 27 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint ac3edf17d34fc39601fc288a8cb9558a2650aaca48b7f565f454bdf747d0b2fb.
def localCycle00115 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Cycle fingerprint ad163acc76aaaa30d736eda30e0cd2662e96003cf6bca712c62eb84167146d8c.
def localCycle00116 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint b19b2fd26c80f05bd49e3a3e224d34a9aad745f90cd7c306f38887d806581c8c.
def localCycle00117 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .gapLower 5 3, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint b19d0b69c4421bbc47f41b9ecd3d02bdef8b68d8ea84f60e906876c50957c61c.
def localCycle00118 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint b1c244979d65a643d8b71657aa0105095b58ae9c5dc4a592f53ada4694abbb96.
def localCycle00119 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 2, .distance 1 4]
    constant := ![-1, 3, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 4, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint b20ca5f50e99915d229c32f6851b34f4658eb1352eb98c2363b0abe3b395485c.
def localCycle00120 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 2, -1, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 3 0, .triangle 17 1, .triangle 18 2, .triangle 23 1]

-- Cycle fingerprint b3720baa4418a4aae86aa4346086020e15d44586cd6962d685022993a7c2b383.
def localCycle00121 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, -1, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 17 1, .triangle 16 2, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint b3f7c423336e0c514a02a5586d466d044ee2a7b6283422937809b453992c5eb3.
def localCycle00122 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 2]
    constant := ![-1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 16 0, .triangle 29 0, .triangle 34 1, .gapUpper 5 1, .triangle 17 1]

-- Cycle fingerprint b48a92d02d97766a862c9efb166909a95f1a34b1d1c882a7e7ab18cef0de2c6f.
def localCycle00123 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 16 2, .triangle 23 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint b494585c15fa3b0c9a6e18a300ae83fad2370415d325401b354b5ff4c793c017.
def localCycle00124 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint b58e1fc3f898d2ef0821168424aff90d05002cf72b3d6c4fb0d4a6b3d16dea92.
def localCycle00125 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 24 0, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint b5b646243293e66f56ba5831b715de236e89fe912104231fe1a3498351a65604.
def localCycle00126 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 4, .distance 2 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 1 2, .triangle 16 1]

-- Cycle fingerprint b9006d9078232897f90f114a747d2df3dedaebcbd90fce16066f029b97650d19.
def localCycle00127 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint ba0904de53fa33d644b298027abe9c811da2cd5ef7d8a413b1e44d538500f5dd.
def localCycle00128 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![0, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 17 1, .triangle 16 2, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint ba63debc3a1bfd4f1df6cd51a5f22a795d02639b4d8c3a4e6d3fd940251e9d2b.
def localCycle00129 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![0, -2, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 19 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint bca183c960bd66148f3dfe6d65086fe2c295db872a4f5d8de15a53786554ee14.
def localCycle00130 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 21 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint bea408d7c2abc2d7946ea6b5c6d3c08e79d043624564a53cc33477d6267f1bcc.
def localCycle00131 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 2, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .gapLower 1 3, .triangle 16 2, .gapLower 1 1, .corridorLower 1 3]

-- Cycle fingerprint bef14d8102401c02962869dc12287d584e9cce566855490c9fdc88e644e5d021.
def localCycle00132 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 17 1]

-- Cycle fingerprint c07eb533c27a1936943465cbad833c1d90693380c11a3aee05d5f47f88b4763f.
def localCycle00133 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .triangle 4 0, .gapLower 1 4, .triangle 22 1]

-- Cycle fingerprint c224e8a1e4aeb22e9b141ac18cad5daca4e8205d2dc819990a02d6162199e0c3.
def localCycle00134 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 16 2, .triangle 23 0, .corridorLower 4 6]

-- Cycle fingerprint c713bcf9dad9e0da821241e26b9bb1c3592050f297df672a6424cf608e72ea09.
def localCycle00135 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint c88290b081bdd1d205b72d38f874fa4a76fb582d7827ec4eb468118bf0425687.
def localCycle00136 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, 0, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 17 1, .triangle 18 2, .triangle 23 1, .triangle 19 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint c9c6e77edee0b55404510bae16f31d436bee63a866cebfab3102ae9f006fc7d2.
def localCycle00137 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 3, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint cb415c0af4ad52d97c2facb43e10f1ce8a0212dc7fef2a68fb7ac19547de2fd8.
def localCycle00138 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint cc3ef9ec3db3d4702cbb8b9ec3a9cc60e46a36333814adf5b29f123dd241f3ad.
def localCycle00139 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-1, 0, 0, 0, -3, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false] }
  origin := ![.triangle 3 0, .triangle 17 1, .triangle 18 2, .triangle 21 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint cd19f4309e7a5afc2a5b7c8b244cec546febcced9a76be334c146f152805dbc8.
def localCycle00140 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .gapLower 5 3, .triangle 7 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint cd89f672b89dde0890db11479f878dcd128493559dfe0f9b9f1c93f4813cfc62.
def localCycle00141 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 2, .triangle 8 0, .triangle 0 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint d6e67394b4e13192d88d93c9726cb54e33519cc4f8aa15189e22e65c9d09f465.
def localCycle00142 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 1 6, .distance 1 5, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6]
    constant := ![2, 0, 0, 0, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, true, false, false, false, false] }
  origin := ![.gapUpper 6 0, .triangle 24 1, .triangle 17 1, .triangle 16 2, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint d732d3e9fce23aa1a758066d73c1ce5e7120d82708b6dc34bcf79b6428ac745d.
def localCycle00143 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 0, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint dae93eb3642cda33fc647811ba2d67e4e3f65d35408a8088d43fc8c6b33de153.
def localCycle00144 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 5, .distance 0 2, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 2, .triangle 7 0, .triangle 0 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint dc12033ed8c91c742c991e9b2b5b21f49163b01ad6078062d459b202c59c5514.
def localCycle00145 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint ddbe3fcf76055e4dc123f15208fbf37d2023778672c33f4b9031c7b6177c9cdf.
def localCycle00146 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![0, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 17 1, .triangle 18 2, .triangle 21 1, .gapLower 1 0, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint e22e8acfb995f2971f6d084742f65ad972a0524a61cd0a902a4d2193c45977c7.
def localCycle00147 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 4]
    constant := ![0, -2, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 19 1, .gapLower 1 0, .corridorUpper 0 1, .gapLower 1 5, .triangle 22 1]

-- Cycle fingerprint e40ae0c84a705b3ea219c3432df57438f0b27f12ccfa25a999241eaa9fa78e01.
def localCycle00148 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint e44fdc600f3f7cc581462ff71073526bc04b55ec5aace79f1549df8ef9fb71ba.
def localCycle00149 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4, .distance 3 4]
    constant := ![-1, 0, -1, -1, 0, -1, 0, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false, true, true, false, false, false, false] }
  origin := ![.triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .gapLower 4 0, .corridorUpper 3 4]

-- Cycle fingerprint e59bdc4351cf1d825cccf602f8bbd3ac9dc12f00eb9243c938bf6f916d43d5dd.
def localCycle00150 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 8 0, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint eb9d20671e3fe9fb634928221af49745716c1d7e0d2bb90d3242831736292e12.
def localCycle00151 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![2, -1, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .triangle 24 1, .triangle 17 1, .triangle 16 2, .gapLower 1 1, .corridorLower 1 3]

-- Cycle fingerprint ebee9e2a83aa8a25b753d8c070d88ea70e39700ac0bae003938057536ed48fea.
def localCycle00152 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 0 4, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 13 0, .triangle 6 1, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint eeca48856513b1f2e00df29adfaf9810d3c01413d0254943815c50da1c4f53b8.
def localCycle00153 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint f12119716dfbf81489c53b75d459668abcf571239ed1012d6f1b803325fce52f.
def localCycle00154 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint f279c56d0eb800deaf876236f5e21d6a6ff47c5b9da505fef3575d556c3262c5.
def localCycle00155 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![-2, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 17 1, .corridorLower 1 2, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint f8724b931d5b3d4cd051648df909d73fedfae8b494e74ec6fb4f44b49a067614.
def localCycle00156 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 1 5]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 18 0, .triangle 30 1, .gapUpper 5 1]

-- Cycle fingerprint f8c284bfd5ef7f6299f86e32830fbcfe6640d81bb6f28d26b1c0050419569c32.
def localCycle00157 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 6, .theta 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 6]
    constant := ![-2, 0, 3, 0, 0, -1, 0]
    coefficient := ![-1, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, false, true, true, false, true] }
  origin := ![.gapUpper 6 6, .thetaNext 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 2]

-- Cycle fingerprint f9922d71e615466619ec3adc4f6525ebdd0ffc95f06de16401f32151177ee66e.
def localCycle00158 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 2, .distance 2 4]
    constant := ![0, -1, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true, false, false] }
  origin := ![.triangle 25 1, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 1, .gapLower 1 3, .triangle 16 0]

-- Cycle fingerprint f9c48f215a7adcc838c174bc329ebe5513b9de6c95cf4a2532362a3b12f4f68b.
def localCycle00159 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 1 4, .distance 1 3]
    constant := ![-1, 3, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 3, .corridorUpper 0 1, .triangle 3 0, .triangle 17 1, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint fab6145da1fcf343050b8768ea872069ea651565542f1923977c2eb2949f332f.
def localCycle00160 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 29 0, .corridorLower 4 6]

-- Cycle fingerprint fd3ba523112913f3a2c25a755f61b80b1e557224fc91d84f7ee00a3dec6ce484.
def localCycle00161 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 6, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 6, .corridorUpper 0 1]

-- Cycle fingerprint fe9afbab58edae452be819fb1fcf9723beb934850cb812bc2a3c7bf40994b3a2.
def localCycle00162 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .triangle 17 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1]

-- Cycle fingerprint ff6120d66d4ad3fb7bedd5a443253350ec463784e94fd07dcb5f6ad463e15458.
def localCycle00163 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 16 2, .triangle 19 1, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

def library : Library := fun id => if id < 82 then (if id < 41 then (if id < 20 then (if id < 10 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 7 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))))) else (if id < 15 then (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)))) else (if id < 17 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)))))) else (if id < 30 then (if id < 25 then (if id < 22 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))) else (if id < 27 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))))) else (if id < 35 then (if id < 32 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)))) else (if id < 38 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none))) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))))))) else (if id < 61 then (if id < 51 then (if id < 46 then (if id < 43 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none)))) else (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none))))) else (if id < 56 then (if id < 53 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)))) else (if id < 58 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none)))))) else (if id < 71 then (if id < 66 then (if id < 63 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)))) else (if id < 68 then (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))))) else (if id < 76 then (if id < 73 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)))) else (if id < 79 then (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none))) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none)))))))) else (if id < 123 then (if id < 102 then (if id < 92 then (if id < 87 then (if id < 84 then (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)))) else (if id < 89 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none))))) else (if id < 97 then (if id < 94 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)))) else (if id < 99 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)))))) else (if id < 112 then (if id < 107 then (if id < 104 then (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none)) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)))) else (if id < 109 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none))))) else (if id < 117 then (if id < 114 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)))) else (if id < 120 then (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none))) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none))))))) else (if id < 143 then (if id < 133 then (if id < 128 then (if id < 125 then (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)))) else (if id < 130 then (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none)) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none))))) else (if id < 138 then (if id < 135 then (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none)))) else (if id < 140 then (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none)))))) else (if id < 153 then (if id < 148 then (if id < 145 then (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none)) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none)))) else (if id < 150 then (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none)) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none))))) else (if id < 158 then (if id < 155 then (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none)) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none)))) else (if id < 161 then (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none))) else (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .tail 62 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20992)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 5, 6], ![2, 1, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 4, 3]], proof := .tail 153 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20993)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 4, 3]], proof := .tail 32 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20994)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 4, 3]], proof := .tail 60 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20995)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 4, 3]], proof := .tail 60 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20996)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 0, 3, 4]], proof := .tail 97 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20997)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 0, 4, 3]], proof := .tail 152 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20998)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 0, 6, 4, 5], ![1, 2, 6, 0, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 4, 0, 3]], proof := .tail 51 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20999)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 0, 6, 4, 5], ![1, 6, 2, 0, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 2, 0, 3]], proof := .tail 113 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21000)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 6, 0, 4, 5], ![1, 2, 6, 0, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 4, 3, 0]], proof := .tail 0 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21001)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 6, 0, 4, 5], ![1, 6, 2, 0, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 2, 3, 0]], proof := .tail 157 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21002)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .tail 97 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21003)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 0, 4, 3]], proof := .tail 152 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21004)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 0, 6, 4, 5], ![1, 2, 6, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 4, 0, 3]], proof := .tail 51 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21005)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 0, 6, 4, 5], ![1, 6, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 2, 0, 3]], proof := .tail 1 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21006)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 0, 6, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 2, 0, 3]], proof := .tail 88 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21007)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 4, 0, 5], ![2, 1, 0, 6, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 2, 1, 0, 3]], proof := .tail 118 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21008)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 6, 0, 4, 5], ![1, 2, 6, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 4, 3, 0]], proof := .tail 0 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21009)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 6, 0, 4, 5], ![1, 6, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 2, 3, 0]], proof := .tail 157 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21010)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 6, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 2, 3, 0]], proof := .tail 77 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21011)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 4, 0, 5], ![2, 1, 6, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 2, 1, 3, 0]], proof := .tail 118 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21012)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![6, 3, 2, 4, 5, 0], ![3, 6, 1, 4, 0, 5], ![2, 6, 1, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 118 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21013)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![6, 3, 2, 4, 5, 0], ![6, 3, 1, 4, 0, 5], ![6, 2, 1, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 106 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21014)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 5, 6], ![2, 1, 0, 4, 5, 6], ![2, 1, 0, 3, 5, 6], ![1, 0, 2, 3, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .low (![18, 4, 126, 46, 89, 35, 76, 142, 91, 82, 12, 107, 66, 162, 131, 133, 10, 151, 44, 9, 73, 63, 57, 158, 33, 16, 155, 72]) }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21015)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 5, 6], ![2, 1, 0, 4, 5, 6], ![2, 1, 0, 3, 6, 5], ![1, 0, 2, 3, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 144 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21016)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 5, 6], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 3, 4]], proof := .tail 99 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21017)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 3, 4]], proof := .low (![23, 4, 126, 46, 89, 35, 76, 142, 91, 82, 12, 130, 66, 162, 131, 55, 10, 151, 44, 9, 73, 63, 57, 158, 22, 16, 98, 72]) }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21018)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 3, 4]], proof := .tail 143 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21019)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low (![108, 71, 126, 93, 78, 69, 15, 121, 38, 21, 129, 147, 61, 159, 58, 54, 111, 128, 119, 83, 132, 100, 40, 80, 84, 161, 124, 14]) }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21020)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 5, 6], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 4, 3]], proof := .tail 105 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21021)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 4, 3]], proof := .tail 138 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21022)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 4, 3]], proof := .tail 25 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21023)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 4, 3]], proof := .tail 141 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21024)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 0, 3, 4]], proof := .tail 115 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21025)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 0, 4, 3]], proof := .tail 92 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21026)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 6, 0, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 4, 0, 3]], proof := .tail 135 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21027)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 4, 3, 0]], proof := .tail 125 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21028)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .tail 115 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21029)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 0, 4, 3]], proof := .tail 115 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21030)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 6, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 4, 0, 3]], proof := .tail 86 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21031)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 2, 1, 0, 3, 4]], proof := .low (![139, 64, 102, 148, 156, 24, 114, 3, 34, 95, 47, 136, 146, 2, 109, 47, 85, 120, 109, 47, 43, 96, 47, 30, 19, 47, 47, 11]) }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21032)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 2, 1, 0, 4, 3]], proof := .tail 94 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21033)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 6, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 2, 1, 4, 0, 3]], proof := .tail 94 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21034)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 6, 4, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 0, 6, 4, 5], ![2, 6, 1, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 2, 4, 1, 0, 3]], proof := .tail 7 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21035)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 6, 4, 2, 5, 0], ![3, 6, 4, 1, 0, 5], ![2, 1, 0, 6, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 2, 1, 0, 3]], proof := .tail 122 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21036)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 4, 3, 0]], proof := .tail 116 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21037)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 2, 1, 4, 3, 0]], proof := .tail 17 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21038)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 6, 4, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 6, 0, 4, 5], ![2, 6, 1, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 2, 4, 1, 3, 0]], proof := .tail 45 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21039)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 6, 4, 2, 5, 0], ![3, 6, 4, 1, 0, 5], ![2, 1, 6, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 2, 1, 3, 0]], proof := .tail 122 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21040)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![6, 3, 4, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 6, 1, 0, 4, 5], ![2, 6, 1, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 2, 4, 3, 1, 0]], proof := .tail 29 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21041)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![6, 3, 4, 2, 5, 0], ![3, 6, 4, 1, 0, 5], ![2, 6, 1, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 122 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21042)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![6, 3, 4, 2, 5, 0], ![6, 3, 4, 1, 0, 5], ![6, 2, 1, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 20 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21043)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 5, 6], ![1, 2, 0, 5, 4, 6], ![1, 2, 0, 5, 3, 6], ![1, 0, 2, 4, 3, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 8 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21044)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 5, 6], ![1, 2, 0, 5, 6, 4], ![1, 2, 0, 5, 6, 3], ![1, 0, 2, 4, 3, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 37 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21045)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 5, 6], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 5, 6, 3], ![1, 0, 2, 4, 6, 3], ![1, 0, 2, 4, 5, 3]], proof := .tail 137 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21046)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 5, 6], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![1, 0, 2, 6, 4, 3], ![1, 0, 2, 5, 4, 3]], proof := .tail 36 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21047)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![1, 0, 6, 2, 4, 3], ![1, 0, 5, 2, 4, 3]], proof := .tail 48 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21048)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 0, 2, 4, 3]], proof := .tail 56 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21049)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 0, 2, 4, 3]], proof := .tail 56 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21050)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 2, 0, 4, 3]], proof := .tail 81 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21051)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 0, 6, 5, 4], ![1, 2, 6, 0, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 2, 4, 0, 3]], proof := .tail 145 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21052)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 0, 6, 5, 4], ![1, 6, 2, 0, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 4, 2, 0, 3]], proof := .tail 26 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21053)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 2, 0, 4, 3]], proof := .tail 81 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21054)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 0, 6, 5, 4], ![1, 2, 6, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 2, 4, 0, 3]], proof := .tail 145 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21055)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 0, 6, 5, 4], ![1, 6, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 4, 2, 0, 3]], proof := .tail 160 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21056)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 0, 6, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 123 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21057)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 6, 0, 5, 4], ![1, 2, 6, 0, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 2, 4, 3, 0]], proof := .tail 127 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21058)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 6, 0, 5, 4], ![1, 6, 2, 0, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 4, 2, 3, 0]], proof := .tail 26 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21059)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 4, 0, 5], ![1, 6, 2, 0, 5, 4], ![1, 6, 2, 0, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 4, 3, 2, 0]], proof := .tail 149 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21060)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 6, 0, 5, 4], ![1, 2, 6, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 2, 4, 3, 0]], proof := .tail 127 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21061)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 6, 0, 5, 4], ![1, 6, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 4, 2, 3, 0]], proof := .tail 160 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21062)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 3, 4, 0, 5], ![1, 6, 2, 0, 5, 4], ![1, 6, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 4, 3, 2, 0]], proof := .tail 101 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21063)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 6, 0, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 134 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21064)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 3, 4, 0, 5], ![1, 6, 2, 0, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 1, 3, 2, 0]], proof := .tail 101 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21065)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 3, 4, 0, 5], ![6, 1, 2, 0, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 3, 1, 2, 0]], proof := .tail 163 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21066)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 3, 4, 0, 5], ![6, 1, 2, 0, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 6 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21067)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 5, 6], ![2, 1, 0, 5, 4, 6], ![1, 2, 0, 5, 3, 6], ![1, 0, 2, 4, 3, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 140 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21068)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 5, 6], ![2, 1, 0, 5, 6, 4], ![1, 2, 0, 5, 6, 3], ![1, 0, 2, 4, 3, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 117 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21069)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 5, 6], ![2, 1, 0, 6, 5, 4], ![1, 2, 0, 5, 6, 3], ![1, 0, 2, 4, 6, 3], ![1, 0, 2, 4, 5, 3]], proof := .tail 49 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21070)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 5, 6], ![2, 1, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![1, 0, 2, 6, 4, 3], ![1, 0, 2, 5, 4, 3]], proof := .tail 87 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21071)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![1, 0, 6, 2, 4, 3], ![1, 0, 5, 2, 4, 3]], proof := .tail 75 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21072)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 0, 2, 4, 3]], proof := .tail 67 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21073)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 0, 2, 4, 3]], proof := .tail 67 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21074)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 2, 0, 4, 3]], proof := .tail 150 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21075)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 2, 0, 4, 3]], proof := .tail 150 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21076)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 0, 6, 5, 4], ![1, 2, 6, 0, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 2, 4, 0, 3]], proof := .tail 28 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21077)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 0, 6, 5, 4], ![1, 6, 2, 0, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 4, 2, 0, 3]], proof := .tail 112 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21078)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 0, 6, 5, 4], ![1, 2, 6, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 2, 4, 0, 3]], proof := .tail 28 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21079)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 0, 6, 5, 4], ![1, 6, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 4, 2, 0, 3]], proof := .tail 68 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21080)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 0, 6, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 150 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21081)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 4, 0, 5], ![2, 1, 0, 6, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 110 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21082)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 6, 0, 5, 4], ![1, 2, 6, 0, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 2, 4, 3, 0]], proof := .tail 28 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21083)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 6, 0, 5, 4], ![1, 6, 2, 0, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 4, 2, 3, 0]], proof := .tail 150 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21084)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 6, 0, 5, 4], ![1, 2, 6, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 2, 4, 3, 0]], proof := .tail 28 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21085)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 6, 0, 5, 4], ![1, 6, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 4, 2, 3, 0]], proof := .tail 68 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21086)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 6, 0, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 53 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21087)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 4, 0, 5], ![2, 1, 6, 0, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 110 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21088)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![6, 3, 2, 4, 5, 0], ![3, 6, 1, 4, 0, 5], ![2, 6, 1, 0, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 79 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21089)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![6, 3, 2, 4, 5, 0], ![6, 3, 1, 4, 0, 5], ![6, 2, 1, 0, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 154 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21090)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 5, 6], ![2, 1, 0, 5, 4, 6], ![2, 1, 0, 5, 3, 6], ![1, 0, 2, 4, 3, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 50 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21091)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 5, 6], ![2, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 3], ![1, 0, 2, 4, 3, 6], ![1, 0, 2, 4, 3, 5]], proof := .low (![23, 4, 126, 46, 89, 35, 76, 142, 91, 82, 12, 130, 66, 162, 131, 133, 10, 151, 44, 9, 73, 63, 57, 158, 33, 16, 155, 72]) }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21092)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 5, 6], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 5, 6, 3], ![1, 0, 2, 4, 6, 3], ![1, 0, 2, 4, 5, 3]], proof := .tail 59 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21093)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 5, 6], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![1, 0, 2, 6, 4, 3], ![1, 0, 2, 5, 4, 3]], proof := .tail 104 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21094)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![1, 0, 6, 2, 4, 3], ![1, 0, 5, 2, 4, 3]], proof := .tail 74 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21095)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 0, 2, 4, 3]], proof := .tail 74 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21096)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 0, 2, 4, 3]], proof := .low (![108, 71, 126, 93, 78, 69, 15, 121, 38, 21, 129, 90, 61, 159, 58, 54, 111, 128, 119, 83, 132, 100, 40, 80, 84, 161, 124, 14]) }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21097)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 2, 0, 4, 3]], proof := .tail 42 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21098)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 2, 0, 4, 3]], proof := .tail 42 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21099)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 2, 1, 0, 4, 3]], proof := .tail 39 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21100)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 6, 0, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 2, 4, 0, 3]], proof := .tail 70 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21101)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 6, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 2, 4, 0, 3]], proof := .tail 70 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21102)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 6, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 2, 1, 4, 0, 3]], proof := .tail 13 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21103)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 6, 4, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 0, 6, 5, 4], ![2, 6, 1, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 2, 4, 1, 0, 3]], proof := .tail 13 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21104)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 6, 4, 2, 5, 0], ![3, 6, 4, 1, 0, 5], ![2, 1, 0, 6, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 27 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21105)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 2, 4, 3, 0]], proof := .tail 70 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21106)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 2, 4, 3, 0]], proof := .tail 70 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21107)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 2, 1, 4, 3, 0]], proof := .tail 13 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21108)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 6, 4, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 6, 0, 5, 4], ![2, 6, 1, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 2, 4, 1, 3, 0]], proof := .tail 13 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21109)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 6, 4, 2, 5, 0], ![3, 6, 4, 1, 0, 5], ![2, 1, 6, 0, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 122 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21110)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![6, 3, 4, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 6, 1, 0, 5, 4], ![2, 6, 1, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 2, 4, 3, 1, 0]], proof := .tail 13 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21111)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![6, 3, 4, 2, 5, 0], ![3, 6, 4, 1, 0, 5], ![2, 6, 1, 0, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 122 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21112)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![6, 3, 4, 2, 5, 0], ![6, 3, 4, 1, 0, 5], ![6, 2, 1, 0, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 5 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21113)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 5, 6], ![1, 2, 4, 0, 5, 6], ![1, 2, 3, 0, 5, 6], ![1, 0, 2, 3, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 31 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21114)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 5, 6], ![1, 2, 4, 0, 5, 6], ![1, 2, 3, 0, 6, 5], ![1, 0, 2, 3, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 41 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21115)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 5, 6], ![1, 2, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 3, 4]], proof := .tail 65 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21116)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 6, 5], ![1, 2, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 3, 4]], proof := .tail 52 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21117)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![4, 3, 2, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 6, 5], ![1, 2, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 3, 4]], proof := .tail 103 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21118)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![4, 3, 2, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 0, 6, 5], ![1, 2, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .tail 103 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21119)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (20992 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 20992 ≤ id.val) (hhigh : id.val < 21120) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 20992)) = true := by
  let j : Fin 128 := ⟨id.val - 20992, by omega⟩
  have hsum : 20992 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (20992 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard164
