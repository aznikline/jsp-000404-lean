import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard083
open N4R2OuterLeftReplay

-- Cycle fingerprint 00966a7422a32b973611918d62740bebd043b205279dcb82c0d826123f810e30.
def localCycle00000 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 6 2, .triangle 12 2, .triangle 3 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint 027d544019302db6033958b49be404c8646c372300689f14be8c4fc8492cfa4e.
def localCycle00001 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 12 0, .triangle 9 1, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 03439e5b6b25f7ef062c272fbd2fc2a8932fce76f76bc8863cc5136af8e4b8f6.
def localCycle00002 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4]
    constant := ![0, -1, 3, 0, -2, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .triangle 2 2, .triangle 12 0, .triangle 28 0]

-- Cycle fingerprint 0406b75ffd33149585e5ae6123033dfa6ca8763c987f717e21a5e245b5510b21.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 13 0, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 051dc96c5500da46b4c37bd870397ba98906eff024b7b88b232f2e4e676f1303.
def localCycle00004 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, -2, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 4 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 0571bfe0264b7ee59309475dc6e528ef078497ce5467bb3e369250e3ca917386.
def localCycle00005 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 3, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint 06cf1db936c7bcbcc6d1932083626716ef21ae434426147db8a6e55ec3b9cc27.
def localCycle00006 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 07139b882223f60040c1e38c7745f83a7cce6289c802aec84bf818cd84aca573.
def localCycle00007 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 12 0, .triangle 2 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint 0a187747674ecf77f978027ec37e48929abfb24b2fbe6d6af7ec0738f336da81.
def localCycle00008 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, -2, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 0ac5f0d6de3d8f21238d7bfb963b1620921243004d2e11d63dc611c7fbc716fe.
def localCycle00009 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 2 2, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 0d97ef15a963b078912bfe8fc8c65409cb675baab71c6dd58990842fe31984d7.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 18 2, .gapLower 1 4, .triangle 2 2, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 0dfc225889118c52fb50736185be743b36a526d036d18e6c413c898cbcf51a1b.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 5, .distance 5 6]
    constant := ![-1, 0, -1, 3, -2, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 3 2, .triangle 14 0]

-- Cycle fingerprint 0e6ea97a4b640d8725a9a4e1f0e8226ff40289217a0c62de0391f77926913f49.
def localCycle00012 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 0 1, .distance 1 3, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 22 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0]

-- Cycle fingerprint 0fc2783aff62c13a95bc6f0b0e8cd21d1cf69c15919f2ec430130ec1174273b8.
def localCycle00013 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .gapLower 1 5, .triangle 2 0]

-- Cycle fingerprint 1046dca0444e7b2849eb06420e4a0d2cd15656ca06326c39dc8407d1cf633ebd.
def localCycle00014 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 10708729dff040ca1acf1305720b075e0f131f0a958c667a2ff554a16352a34c.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 4, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 2 2, .triangle 6 1, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 135f0f78678bcf4300f34ac31c3ab5e5de921e377bfc5076cf949fdcbf111142.
def localCycle00016 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5]
    constant := ![-1, 0, -1, 3, -3, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 4 2, .triangle 13 1, .triangle 12 0]

-- Cycle fingerprint 153929c7c45ae76c5e7bfb39bdeddf3e991c446cc76eb9dc80d2117dc6aa947e.
def localCycle00017 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 1562d17ebc77f06e3ae43d53ea326e676a872cbc302b3effd9298ce6ba189317.
def localCycle00018 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 3 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 171db11094b986e0d337aeff2e6c1114b12b204a4cfb7eb294c93aeadea10850.
def localCycle00019 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, -1, -1, -2, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 16 2, .gapLower 1 4, .triangle 3 0, .triangle 1 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 1af16771fedc39f49c765fd6ed81abc08e7d68cf92b7d722310b363fc3a23c67.
def localCycle00020 : Cycle where
  length := 15
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 3 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint 1c322e187c5982f4ce8ffb1cd86b522937a4036dcc3d73c4cd0f312e64568d31.
def localCycle00021 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 2 3]
    constant := ![-1, 3, 0, 0, -2, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .gapLower 1 2, .triangle 1 0, .triangle 15 1]

-- Cycle fingerprint 1ccf3d87df0314aa1842589c3d3dc3d0155688f5ea1c3f0af2a046f15d55ba48.
def localCycle00022 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 20 1, .triangle 21 0, .triangle 33 1, .triangle 34 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 1d9ac0345968f9932dcca0391bf2600caf63ab5aa73b24fa5d60c7e171e8b1d7.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 3]
    constant := ![0, -1, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, false] }
  origin := ![.triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .triangle 1 0]

-- Cycle fingerprint 1e3b05e7be3372a37a4245084a710a78c4eb2ed14e89213f6e53cae999d4606c.
def localCycle00024 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 12 0, .triangle 2 1, .triangle 1 0, .triangle 15 1, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 2083fe65eefe9d507d5d347c88a6bab23286cd1553b3c9ea84120318d2731b64.
def localCycle00025 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5]
    constant := ![-1, 0, -1, 3, -2, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 2 2, .triangle 12 0]

-- Cycle fingerprint 213ac813c76d2e30b78d3a1d9a2aea56565673b0d36783e8a32eb86cf2201570.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 5]
    constant := ![0, -1, 3, 0, -3, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 3 2, .triangle 14 0, .triangle 30 0]

-- Cycle fingerprint 21b7bcbd8c97120b443f97dfd4ca041b8d737f6f19f5b0b4704478e01c8980c2.
def localCycle00027 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, 0, -2, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 24 1, .gapLower 1 2, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 21f8a07af191796f26dc1c3637f8d6ff127f4bc80ae7001b9b7ef3d22893036d.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 3, .theta 1]
    constant := ![0, 0, 0, 3, -2, -1, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 4 0, .triangle 1 0, .gapLower 1 0]

-- Cycle fingerprint 2224227365704f59ce3eecc3a7cc60ecadd0db62bc07eec30f4301e31370ca8a.
def localCycle00029 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 2, .distance 0 1, .distance 1 3, .theta 1]
    constant := ![1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 0, .triangle 1 0, .corridorLower 1 3]

-- Cycle fingerprint 2340306501cb4446bb01db92994a24671a5899c606838585d433313a95120445.
def localCycle00030 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 26cb6d52a5f1ea767d3a53cb93a3d53030e6470136c5bf28c911d4ee9de04b42.
def localCycle00031 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 5]
    constant := ![-1, -3, -1, 0, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 3 0, .gapLower 1 1, .corridorLower 1 3, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 2]

-- Cycle fingerprint 2855ef4885db0f71eb9e7140dd19918cb0a30dfa6d6544690ebb141b20adbea4.
def localCycle00032 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 1 6, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint 2f723cfed228bcdd861a7965a8c28ad95f7f25a55a47bf9306b3e47de5a63203.
def localCycle00033 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 2fcfcc87cce986f59eed78d4e7032540685e1645c590bff0bfba401fb907cbfc.
def localCycle00034 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 302981b1c3f375e5653a79de13e5d15a44f57840b0a1ee2f631995b637128655.
def localCycle00035 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6]
    constant := ![-3, 0, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 2, .triangle 1 2, .gapUpper 3 3, .gapLower 6 5]

-- Cycle fingerprint 30b956492b2f2ae2864a01454348f5d73a094c64d61145e98834136554698726.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 3, .distance 2 3]
    constant := ![-1, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .gapLower 1 3, .triangle 4 0, .gapLower 1 1, .triangle 15 1]

-- Cycle fingerprint 32e97fd15019c96edd440cca592e1d318f189b31ef9a3ec115c9b6a727cae9e1.
def localCycle00037 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 33a1eff762f7928019db9b064e8986eed55d9ed787fa5e2cf5e4b51a56796e3d.
def localCycle00038 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6]
    constant := ![-3, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 18 2]

-- Cycle fingerprint 35cd8013b6b47dcd8aa6549186ac32b97761dda7470018b5cc1164a65dc273d0.
def localCycle00039 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 16 2, .gapLower 1 4, .triangle 3 2, .triangle 12 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 3c89608f3cacbdf22097b1ec7acbb9497f35b0c93ac79c19dd4055b28256a1bc.
def localCycle00040 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 3 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 3cc22a947508058df5d43a2b617c9ae2f45259c011efce5aa1a7b7614385f85e.
def localCycle00041 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, 3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 3 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint 3d7d70b293254cadfe8d7794cf6a4da1913da925b21ea56561888ed4c6e67776.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, -1, 3, -3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 2 2, .triangle 13 0, .triangle 34 1]

-- Cycle fingerprint 3db2cdf377405f9f14aca09f4b68a26f731157edba8a0ce277cc7797690fcfeb.
def localCycle00043 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 5, .distance 4 5, .distance 2 4, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 2 0, .triangle 3 0, .triangle 22 1, .triangle 28 0, .gapLower 4 0]

-- Cycle fingerprint 3e64782325ac0649f7a75ac124eac11ae43c3d8d1ce6639282931871a1cf64be.
def localCycle00044 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 24 1, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 43405380b529ba9c112505690152a33eec21de31ec0f32508c70ff5801bf01f7.
def localCycle00045 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 6 2, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 436b775bdffef00fdebd6b137b3766789761d1dff528688f56e3099ca2584b94.
def localCycle00046 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 2, .triangle 2 0, .triangle 3 0, .triangle 22 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Cycle fingerprint 43de1865193b4be51e5f7486d5f97b7489f63febea1886c539c8c3d5830c29fd.
def localCycle00047 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 3, .theta 1]
    constant := ![2, 0, 0, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 16 2, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .triangle 1 0, .corridorLower 1 3]

-- Cycle fingerprint 449efaa1be83dae35ba9bdf774322e700f68734cbdec8301fadfcc4b842ce26c.
def localCycle00048 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 16 2, .gapLower 1 4, .triangle 3 2, .triangle 14 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 48f3294e02267abf223a496384af84f9d1a1c8f45572bf37f0b1b43689f8de66.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, -1, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.triangle 1 0, .triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint 4a46206436dfd60dbfd1b755e6c9d52c29778e9075e86793d4d0998d6ea9fc5d.
def localCycle00050 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 0 1, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2]
    constant := ![-2, -1, -1, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 2 0, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 4bcf64faf1c0b2df06fdf91535f385e2de4f0ef58c8ee5a9e7986b7ee5b1eed2.
def localCycle00051 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, -1, -1, -2, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 18 2, .gapLower 1 4, .triangle 2 0, .triangle 1 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 4c2e74b029df501eff4cd337d525651f24fbf3f72175f426f93663470d291325.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 5]
    constant := ![0, -1, 3, 0, -2, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 3 2, .triangle 14 0, .triangle 30 0]

-- Cycle fingerprint 4c82de9678a15c3d565ba5bb16530aeae5eafad853905df039aad7b4ab5fed3a.
def localCycle00053 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 2, .distance 0 1, .distance 1 3, .theta 1]
    constant := ![2, -1, -1, -2]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 0, .triangle 1 0, .gapLower 1 0]

-- Cycle fingerprint 4ea7ffe7578d4e049e93b12db51f05b6af5dcfb00663c77f8175c60910daab98.
def localCycle00054 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 34 0, .triangle 14 0, .triangle 12 1, .triangle 2 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint 4f0f20ac5076fcad83135bb6a27b9baa0ac8cf7230381b96e7029daabac30947.
def localCycle00055 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-2, -1, -2, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .gapLower 1 1, .triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint 54a24bc318b7f2edfde5f5fb5c0208316926843dd1cad6eabf2ba69db1d31398.
def localCycle00056 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, -1, 3, -3, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint 5576506980cf9e201ef8cf01b90a3ffb6b91fffd9d2ef610e43d87e97ecd9b47.
def localCycle00057 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 2 3]
    constant := ![-1, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .triangle 3 0, .gapLower 1 1, .triangle 15 1]

-- Cycle fingerprint 5805db678bf6328c92a9511dccf3257a296f05357e0cb0c020fe50fb733f69df.
def localCycle00058 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 13 0, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 5841e89811bc859fc63de252f17200ef8a8237af8b240712e3bade797c84cf24.
def localCycle00059 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, -1, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.triangle 1 0, .triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint 5927a8388a8334f1812ff6ca183731b7d385175f37e0f26c4fce12a4caab8e38.
def localCycle00060 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 3, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint 5d73e8accd54f6d861750c9fd4b41a29ee40c7ad007179bf43d1b1904b45757a.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 4, .distance 0 5, .distance 5 6]
    constant := ![-1, 0, -1, 3, -3, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 2 2, .triangle 12 2, .triangle 14 0]

-- Cycle fingerprint 5e29f29680339a5164dc989c89d8022feaa528ba15801bee92dcc6b4bd323934.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 5f7af76a216673f45998e01dbbcce5e0a8e7b0bf46d511a989a02af9eb9f5fb6.
def localCycle00063 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 61aa30451a618aca53adc49bcf7a425fa67fc7434e5ef3ac23879d981da825be.
def localCycle00064 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, -2, -1, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, false, false, true, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 18 2, .triangle 23 1, .gapLower 1 3, .triangle 3 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint 62f4f5bb7575ae02566506196a907ac9ca42fef2cde5f3baf4d4877eb1e92aae.
def localCycle00065 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 3 0, .triangle 22 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Cycle fingerprint 65bbc8821f579d4753b0852ac542daccd2f4bf2283e4fad989ccc4303eda60b7.
def localCycle00066 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 4 0, .triangle 18 1, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 67deb7b11c2d9a78bf4947d656a1207a236f1d28bd657076fc332634a6005262.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 34 1, .triangle 12 0, .triangle 2 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint 68ee6cb2321cf8cadab706f770f90f2cbc56d1d30793c004a1b15c89dc2f327a.
def localCycle00068 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, -1, 0, 0, 3, 0, -1, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 6bb20ac965e70c00fa9b8e6a43a748263d5a689775e0c65424421add4df9283d.
def localCycle00069 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 2 3]
    constant := ![-1, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .triangle 3 0, .triangle 1 0, .triangle 15 1]

-- Cycle fingerprint 6f57303ed21c27ac788ae910282d226637c134336d62ac6f5a3ec5b2c31c9db7.
def localCycle00070 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, -1, 3, -2, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.triangle 1 0, .triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 22 2, .triangle 24 2, .gapLower 1 2]

-- Cycle fingerprint 7271edde9dc7eb4f5dcedb15b82152d1acfed7485092167394ae3d2137e17046.
def localCycle00071 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-2, -1, -2, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 3 0, .gapLower 1 1, .triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint 7299896991a8d60f06e2e584a75bb1c4a4a765e2f01c7cacb6d87fa102668d85.
def localCycle00072 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 2, .triangle 13 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 74d62cbe2411ed006e00d63f018836326a8c62ecc6928146a3899d29e5fabcb9.
def localCycle00073 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 20 1, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 754dd6571ea8b0c39ec878e53f94ab5bd68eab804274160fe4f434e6c90e8106.
def localCycle00074 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4]
    constant := ![0, -2, 0, 0, -1, 0, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false, true, false, true] }
  origin := ![.triangle 22 2, .gapLower 1 3, .triangle 4 2, .triangle 13 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 2]

-- Cycle fingerprint 763736a6ad576d6b3718599e42b9c025d2ad877e332476376a0f9f96de9e4c02.
def localCycle00075 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 4, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 5]
    constant := ![2, 0, -1, 0, -2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, false, false, true] }
  origin := ![.gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 19 2, .gapLower 1 3, .triangle 3 0, .gapLower 0 1, .gapUpper 3 3]

-- Cycle fingerprint 76a596373880075eb6df75c3fac217c217437798c59187da89cd56a3bfd857d4.
def localCycle00076 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 4 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 23 1, .triangle 34 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 78d825cfde92593b3a2701fbfe6ec205c36f790221918b55f5a24be8e2229e84.
def localCycle00077 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 1, .distance 1 3]
    constant := ![0, -1, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .triangle 22 2, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint 79584a8d20dc26e3cf2a210b483ca4b96494992279c1cbe28500ec942c926276.
def localCycle00078 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, -2, -1, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, false, false, true, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .triangle 3 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint 79bc0ef238e0985c5eca508aca36ad1d3b763dfdb69ca5fb6f6f4edaad9e5713.
def localCycle00079 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4]
    constant := ![0, -2, 0, 0, -1, 0, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false, true, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 3 2, .triangle 12 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 2]

-- Cycle fingerprint 7c19195d87d8334f69b210b29bb9b4cd6824ae954c1739d46191dbcd68746864.
def localCycle00080 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 3]
    constant := ![-3, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .triangle 3 0, .triangle 1 0]

-- Cycle fingerprint 7c58aeb0bfd10251a79a85693f394f15791acf1a8e7dd9d92ecefead74192240.
def localCycle00081 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 22 1, .triangle 34 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4]

-- Cycle fingerprint 7c76af30e606c2f5c3a21a3f6a85adbebab66fa36ec48536adb305bbfd79c015.
def localCycle00082 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 24 1, .triangle 34 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 7d7e1d0dd5386a159baaf94400caa63ea3a1e0ff348a02de9a6c21d6a2999beb.
def localCycle00083 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 0, .triangle 28 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 801f6f3cc54f3320da34c30d589b8b1c8da13c8472c3d3b47b1aa00070c1d567.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 3]
    constant := ![0, -1, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 24 1, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint 80b3a5c8461a97e0125b9c8e3c7b4eca40cfe0ed9ff09282cab62cbe8c47d9d5.
def localCycle00085 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 22 0, .triangle 12 0, .triangle 2 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 81cc3b5c9fcf724812aac963f88b8a81fe08dff41cdb0754e7c4100d649c51b6.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, -1, 3, -2, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.triangle 1 0, .triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 23 2, .triangle 24 1, .gapLower 1 2]

-- Cycle fingerprint 867a1486f4890c9604c2caa565adbf5c698a544c72bfa4976dfab934b14a093f.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 23 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 8888ef412069e070a479ccc85a72929a3b30e4b32c9df37fa7b226150126f86c.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 1 2, .gapLower 1 1, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint 898539bf02acee35bed1f80bf8f68dab81173520dbc7b66bdd670796d4f9a4dd.
def localCycle00089 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 3, .distance 2 3]
    constant := ![-1, 3, 0, 0, -2, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .gapLower 1 3, .gapLower 1 2, .triangle 1 0, .triangle 15 1]

-- Cycle fingerprint 89ecc49533558332e36a83c7cd1d775096819e15a4e474c5ab71c52b354e8f18.
def localCycle00090 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 1, .distance 1 3, .theta 1]
    constant := ![2, 0, 0, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 18 2, .triangle 23 1, .triangle 22 2, .gapLower 1 2, .triangle 1 0, .corridorLower 1 3]

-- Cycle fingerprint 89fb0a03091232cf436488925044904825acad2f50b3c055768507acc1c84ffe.
def localCycle00091 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-3, -1, 4, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint 8acad4dfe5dd33813b3f09e1d67cc1986bd1021210501d694caea36df8727464.
def localCycle00092 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 2, .triangle 22 0, .triangle 12 0, .triangle 2 1, .triangle 1 0, .corridorLower 1 3, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 8b9f0d103d7ad31febebd968e404300523baf28aab683a2548a77501df69133f.
def localCycle00093 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 5]
    constant := ![-1, -2, -2, 0, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 3 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 2]

-- Cycle fingerprint 8bd62524e5b0fb3ac77b48bb5b687947832103ee38cecd88823caefa30ea603f.
def localCycle00094 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 1, .distance 1 3]
    constant := ![0, -1, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, false] }
  origin := ![.triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .triangle 1 0]

-- Cycle fingerprint 8ced7de830e0452febd65a46d28b68e9e23c8ea2dd53bf94eab6fb65a51c4f12.
def localCycle00095 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 34 2, .triangle 13 0, .triangle 2 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint 8ebe1f9c23c4a4a2084123724e3b82f7d71c21e8dbf6a4d75bc52dfbc8a33408.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .theta 1, .zero, .theta 6, .distance 5 6]
    constant := ![0, -1, -1, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 23 0, .triangle 2 0, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 8fdb3abb2c3607996657449e7870e587f2b372d49815dbb6e7893f74b8912df1.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 907e1c6d02a1c94f69492af10021589b382fcd360bc03227b13b017b3393f7fa.
def localCycle00098 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4]
    constant := ![0, -1, 3, 0, -3, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .triangle 2 2, .triangle 12 0, .triangle 28 0]

-- Cycle fingerprint 938bfef36f794f932ce826edcb916422f9829adbad16a222a944dd626fb8cb87.
def localCycle00099 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 12 0, .triangle 2 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 9a63764cfb6320fb3bd3d29e5aeac5381d2dedbd2861e18e009fff396056652a.
def localCycle00100 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5]
    constant := ![-3, 0, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 2, .triangle 1 2, .gapUpper 3 3, .gapLower 5 4]

-- Cycle fingerprint 9bfa1934330a02a5a4a6cfab5a386170d66ac076836118fe01d01bb241a15d75.
def localCycle00101 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 6 0, .triangle 28 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint 9fbbd67a5a7a19d9f77dd042fa339885e7fbe48d6f303dd6c1bd2e6dc2b381a2.
def localCycle00102 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-3, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 2 2, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint a1c4c8cbf30e3baeaf47a38409c8207bbc0d052439eaa51590736f4951baf896.
def localCycle00103 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 24 1, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint a4d16b7917c33bdf4bd765612deca67699f89ec625535d1caea469a2b74d433a.
def localCycle00104 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .theta 1, .zero, .theta 6]
    constant := ![3, 0, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 2 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint a5c2476f6789bb9b21faf31b7385078b89565d6414ab30c6f1909bbedac62137.
def localCycle00105 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 14 0, .triangle 3 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Cycle fingerprint a6d8b6bc54b73b0f4060a4e4008250a9f6ee91440c3a1d4488bd33e70bf4e732.
def localCycle00106 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 0 1, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 24 2, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 22 2]

-- Cycle fingerprint a70559edf076353f0252574aa27ef8d09e6c620425bb5de401c8aa9a0748e081.
def localCycle00107 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 2, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 2, .triangle 18 0, .triangle 0 2, .triangle 6 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint ab238e0a3220d2194c44060cce99cf1c15cbfac71a1c8b2d082c22c2b0640695.
def localCycle00108 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 0 4, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![0, 2, -2, 0, 0, -1, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint adfe2336b164e900f2887640d41194996ba8d42470114985aa407d11bcc1b467.
def localCycle00109 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, -1, 3, -2, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 24 1, .triangle 3 0]

-- Cycle fingerprint ae929b8d13c743d46c87a76e78ccb81c25fef0d01634cb4e37645fa51fa835b0.
def localCycle00110 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 23 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint b13e3ca157dc9975e2f6bf16ad8cb4724aaff257cc75fd092f40bf224a3562ca.
def localCycle00111 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint b18abdb25d3dd7bc314eeead845cc33ea6cbb46e1fb32b49a72fa6c4167b48d2.
def localCycle00112 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 3 0, .triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 24 1, .triangle 34 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint b1b2279ba876a42e4f16c9bd3f81cef139fad2ea6930529d9792f4c255d9ab72.
def localCycle00113 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 2, .distance 0 1, .distance 1 3, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 0, .gapLower 1 1, .corridorLower 1 3]

-- Cycle fingerprint b21b163928d9b7c341aa5cc741d286960a60339cc29312b4982edac37009cc3e.
def localCycle00114 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, -1, 3, -2, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 2 2, .triangle 13 0, .triangle 34 1]

-- Cycle fingerprint b3c0e120138f102c57e6dc9447ab6ce945ccb6014092ffc302cdc01d124024c6.
def localCycle00115 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 24 1, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint b4e6c9df770a883c35b1ddc357f840b484784a504df4ff70f751d9aa8099da43.
def localCycle00116 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, -1, 0, 2, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 2, .gapLower 1 4, .triangle 4 0]

-- Cycle fingerprint bd6adde1d6a862c0edfc44c008c85c34d71b88eb0b996c31505a9d3a03abef3b.
def localCycle00117 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 2, .triangle 10 1, .triangle 11 0, .triangle 21 2, .triangle 23 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint bdc9103d4b2378a283f460475b3abc3637051793572e093fa2d803ef9674da0b.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 24 0, .triangle 34 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint c039eccbd7029cddb44e934d37b8df799a8c9f15c2bdeced09be7f8634f87a6f.
def localCycle00119 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 12 0, .triangle 2 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint c24d5db602930768eb34f7f5fc05d74e9adf2514e829a4c55fe67038acc7b9d4.
def localCycle00120 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 3, .distance 2 3]
    constant := ![-1, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .gapLower 1 3, .triangle 4 0, .triangle 1 0, .triangle 15 1]

-- Cycle fingerprint c3131abd233b9ef856a1505dc7f17c573da04ffc8f5b1ff05b49f4db6b198ba2.
def localCycle00121 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 5, .distance 4 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 2 0, .triangle 3 0, .triangle 22 1, .triangle 28 0, .gapLower 4 0]

-- Cycle fingerprint c3dc205e3e069f39fdce8dd179646f98c50f447e9371047f3c990f4a7edaf692.
def localCycle00122 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, -1, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.triangle 1 0, .triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 22 2, .gapLower 1 3, .triangle 4 0]

-- Cycle fingerprint c5ada212e129912bf41688f307569446c63ef853aa12a22d1c4492786a370bfe.
def localCycle00123 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -1, 3, -3, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 2 0]

-- Cycle fingerprint c7203a25550712ca56eedb7959cc1a8cc59e327f7d88e7e5fb349a2d4e3ec26a.
def localCycle00124 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 3]
    constant := ![0, -1, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 24 2, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint cb11f078cb63df346bf6d3ee044f8f699c1de521b1c36522e4402f1280d89254.
def localCycle00125 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint cc841cc721f67d9d31e38f0e16f465464e40721f1105ec963dba2edef1eb8d85.
def localCycle00126 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 24 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint cc90720682e161bc42ff3c339def8fd3682ffcff92259cd721699af2f21bb7e4.
def localCycle00127 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6]
    constant := ![-2, -1, -2, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 2 0, .gapLower 1 1, .triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 18 2]

-- Cycle fingerprint cdf84cdffd69bdd143ac1128f83f50956f38e226a908e0fb507be176512ecb9a.
def localCycle00128 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 22 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint cf7b0672276222d6e80e6f96a80cfdc9f25aa35da08be785bf31fdfbe8059bbf.
def localCycle00129 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint d0f9767f684699e7519b1d1045f311fb9a4ef0a671838cb990996966483543a1.
def localCycle00130 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint d106aff462b54b9106f1d185247f9df6dd5912041be8c99c933d63d58da7e61e.
def localCycle00131 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 16 2, .gapLower 1 4, .triangle 4 2, .triangle 13 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint d117cc23a7945410934e068b568a678f52e861186c153dca778d4a2612cbbb3e.
def localCycle00132 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .theta 1, .zero, .theta 6]
    constant := ![3, 0, -1, -1, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 2 0, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint d1308b82786d1c6e6125cb6872cb13b7ee6abe70f458a220273e06cb06aede7c.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 2, .triangle 14 0, .triangle 24 0, .triangle 22 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint d257c89d6053a469b29a3e536392c1a0f22fb7b3b533e20678431b7fb59220ab.
def localCycle00134 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1]
    constant := ![-1, -2, 0, 0, 0, 3, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .gapLower 1 3, .triangle 4 0]

-- Cycle fingerprint d387e590c2019b90836c0cafec5f567ca9843fccbb838e194fc5176239d13de3.
def localCycle00135 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-3, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint d3e7cc20abaa2b1d27553070e7d87db18982f6804ac83d84ba4906c55cb10d1a.
def localCycle00136 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint d5cd74f64438092ca6fe745e8b285e46158e8a5e2a670ba4cd0f68fca3946d10.
def localCycle00137 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 5, .distance 0 1, .distance 1 3, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -2, -1, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 3, .triangle 3 0, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint d772c717c54c026812704bd2e8ee5b28700ee8a2780ecae98dd8a856bf8cd29e.
def localCycle00138 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4]
    constant := ![0, -2, 0, 0, -1, 0, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false, true, false, true] }
  origin := ![.triangle 22 2, .gapLower 1 3, .triangle 4 2, .triangle 14 1, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 16 2]

-- Cycle fingerprint d77817e9a7cf273b4cb314bc439825a6308dc6d6f91a801f266161b9ddbb1eae.
def localCycle00139 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -1, 0, 2, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 18 2, .gapLower 1 4, .triangle 2 0]

-- Cycle fingerprint d7b5287e4f6fba9863ed6748b3d8571c9f88ac4071ddac77571cef6f7cc1fc1c.
def localCycle00140 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint d7dd8eae20ebcc7154ce5f0248956d9a90cd82971611ef454f4f9c63eb6224ec.
def localCycle00141 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![0, 2, -2, 0, 0, -1, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint d993a2a12c104d318da621e529a0f0dfa020c7ae19edf177ed28ec7bd85dcab5.
def localCycle00142 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 5, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 6]
    constant := ![0, -2, 0, 0, -1, 0, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false, true, false, true] }
  origin := ![.triangle 23 1, .gapLower 1 3, .triangle 3 2, .triangle 12 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 18 2]

-- Cycle fingerprint dc2cb4df9394b97c8e40267d461e3f8b3a93f6c89553f26246c0728bf5682178.
def localCycle00143 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint e1c9fe163380e292fd3d7715b632e1ec4fba28cefa5a746e7f94189a79becce3.
def localCycle00144 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 3, .theta 1]
    constant := ![2, 0, 0, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 1 2, .triangle 1 0, .corridorLower 1 3]

-- Cycle fingerprint e311739e981251b3f397732e10a6cf3be9f25895ffc4b4b6efdc5d99482b1865.
def localCycle00145 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 0 2, .triangle 6 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint e500149105668b02d1215592906909673c202005a288863e67887799111a57dd.
def localCycle00146 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint e62a037ee093c4b47a3abd985fa848fa8a2a22102500950292bf882aaed7814f.
def localCycle00147 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 4, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 2 2, .triangle 6 1, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint e672062f4b3269a0fc4c6ad39af7874a649050c76b445e97dad5600aec83460c.
def localCycle00148 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .zero, .theta 6, .distance 0 6, .distance 0 2, .distance 2 4, .distance 4 5]
    constant := ![-1, 0, 0, 0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaLower 3, .thetaUpper 6, .gapUpper 6 0, .triangle 8 1, .triangle 6 0, .triangle 28 0]

-- Cycle fingerprint e6a6903f74d0c0eb5551bc5182ab9a4f14795a870b8d9c4294cb342549a224e0.
def localCycle00149 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 4, .distance 0 5, .distance 5 6]
    constant := ![-1, 0, -1, 3, -2, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 2 2, .triangle 12 2, .triangle 14 0]

-- Cycle fingerprint e8d1fa286367c572ec9837dac94a2c8b6f74f2526cc074b0a7044dff45bed8be.
def localCycle00150 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 0 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![0, 2, -2, 0, -1, 0, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 2 2, .triangle 13 0, .triangle 34 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint e93ec11c39c9bb1d2347dfe3e010ae8d8d6db251539851773afb5b800ffa2e46.
def localCycle00151 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 3]
    constant := ![0, -1, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, false] }
  origin := ![.triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 4 0, .triangle 1 0]

-- Cycle fingerprint e9b3d01dcd347cd758a454e062c14b12e0c1f6276f05af240c726edd1af8fb54.
def localCycle00152 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1]
    constant := ![-1, -2, 0, 0, 0, 3, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint ea20e2d3b07942ea3c452c9bd84e26a796dd3fcb593c9a0165649fc475a7f347.
def localCycle00153 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 4 5, .distance 2 4, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 3 0, .triangle 22 1, .triangle 28 0, .triangle 29 0, .corridorLower 4 6]

-- Cycle fingerprint edebaf0b6c5f90a5e74e0732788f75a618a397b93293969e2030c963dfe31c00.
def localCycle00154 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 6, .distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, -1, -1, -2, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 16 2, .gapLower 1 4, .triangle 4 0, .triangle 1 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint ee72c6ac1a5b517c89b84b25a80a6d4e378339d024d311b4ca7c171f8e87779d.
def localCycle00155 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 4 5, .distance 2 4, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 2, .triangle 4 0, .triangle 3 0, .triangle 22 1, .triangle 28 0, .gapLower 4 0]

-- Cycle fingerprint eecfae7a262ca6b32d8b7b52399614a3bc8c7ba1c7f2da33f83fbe1fb678516a.
def localCycle00156 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, 3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 0, .triangle 28 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 1 2, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint f07bb223664e6fbe24e263cce148fcca57b11e1d6e285dddeb96b1b268cde474.
def localCycle00157 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-3, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 3 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint f0f091fcf46e3ef8fdbfaadc1700c6186a654385d49567758436495c19318ee8.
def localCycle00158 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 0 4, .distance 4 5]
    constant := ![-1, 0, -1, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 2 2, .triangle 12 0]

-- Cycle fingerprint f21f0d373605c7c09ae7114658f4eace27ec6a2f14cf466795aba790aebd82d0.
def localCycle00159 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint f4dc4b884f06eff7ce21ff65a8f878f2db8e972aa2deb56600e415a620cc3b70.
def localCycle00160 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint f71b4cda2aebd5fd15f4d1ca438e42bc7a326cc71a6139ba5a71ece5ce06ff85.
def localCycle00161 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 0, .triangle 28 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint f94f18c8b95d34d22502302cb9c16af4df5eaf151cd2df656fdfdbe1d53b1b3d.
def localCycle00162 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 2, .triangle 10 1, .triangle 11 0, .triangle 33 1, .triangle 34 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint f993938e50e1fe310ae1417be24c99bebe5078d8fd99a4e4f52d7d7dd1685cfc.
def localCycle00163 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![-3, -1, 0, 2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 3, .triangle 3 0, .gapLower 0 1, .gapUpper 3 3, .gapUpper 5 5, .gapLower 6 5, .triangle 23 0]

-- Cycle fingerprint f9edab848d8c6a8958902815c0397db9af31031485edbed0a756f0564d0c636d.
def localCycle00164 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 13 1, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Cycle fingerprint fa0f95690afb88017e043e12e98ea4a1b3c15a48b7331888f793bf7603b8e810.
def localCycle00165 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 4 5, .distance 2 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 3 0, .triangle 22 1, .triangle 28 2, .triangle 30 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint fa27cd8d12cc0ea8011f5bd296fd173f4f13d2384bff5b1902f436dd285d79a4.
def localCycle00166 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint fa7f4db588f0cd426cbc2752d7225735acc79823f551b48c509dc6037c83b66f.
def localCycle00167 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 1, .distance 1 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 0 1, .triangle 3 0, .triangle 22 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint fc025a242b51ec0103af12f67cae693ba7874750b922c547daebab6046064290.
def localCycle00168 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint fc5a053f2633fed0a94e98cf7bbdb08c0400fdc353ed16bf7d2e2871d0d831ad.
def localCycle00169 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint ffdea6bedb254e95ad2501e22d536e11d53342ad847844d39c20da12b7b8d752.
def localCycle00170 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 6 2, .triangle 12 0, .triangle 34 0, .triangle 30 2, .gapUpper 2 4]

def library : Library := fun id => if id < 85 then (if id < 42 then (if id < 21 then (if id < 10 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 7 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))))) else (if id < 15 then (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)))) else (if id < 18 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none))) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)))))) else (if id < 31 then (if id < 26 then (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)))) else (if id < 28 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none)) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none))))) else (if id < 36 then (if id < 33 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none)) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)))) else (if id < 39 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))))))) else (if id < 63 then (if id < 52 then (if id < 47 then (if id < 44 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none)) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)))) else (if id < 49 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))))) else (if id < 57 then (if id < 54 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)))) else (if id < 60 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)))))) else (if id < 74 then (if id < 68 then (if id < 65 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)))) else (if id < 71 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none))))) else (if id < 79 then (if id < 76 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none)))) else (if id < 82 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none))) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none)))))))) else (if id < 128 then (if id < 106 then (if id < 95 then (if id < 90 then (if id < 87 then (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)))) else (if id < 92 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none))))) else (if id < 100 then (if id < 97 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none)))) else (if id < 103 then (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none))) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)))))) else (if id < 117 then (if id < 111 then (if id < 108 then (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none)) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)))) else (if id < 114 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none))) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none))))) else (if id < 122 then (if id < 119 then (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none)) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)))) else (if id < 125 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none))) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none))))))) else (if id < 149 then (if id < 138 then (if id < 133 then (if id < 130 then (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none)) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none)))) else (if id < 135 then (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none))))) else (if id < 143 then (if id < 140 then (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none)))) else (if id < 146 then (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none))) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none)))))) else (if id < 160 then (if id < 154 then (if id < 151 then (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none)))) else (if id < 157 then (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none))) else (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none))))) else (if id < 165 then (if id < 162 then (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none)) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none)))) else (if id < 168 then (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none))) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![3, 1, 4, 5, 6, 2], ![3, 0, 5, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 5, 4, 6], ![2, 0, 5, 1, 3, 6], ![2, 0, 4, 1, 3, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 92 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10624)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![3, 1, 4, 5, 6, 2], ![3, 0, 5, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 5, 6, 4], ![2, 0, 5, 1, 6, 3], ![2, 0, 4, 1, 3, 6], ![2, 0, 1, 4, 3, 5]], proof := .tail 85 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10625)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![3, 1, 4, 5, 6, 2], ![3, 0, 5, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 0, 5, 1, 6, 3], ![2, 0, 4, 1, 6, 3], ![2, 0, 1, 4, 5, 3]], proof := .tail 99 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10626)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![3, 1, 4, 5, 6, 2], ![3, 0, 5, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 5, 6, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 1, 3, 6], ![2, 0, 4, 1, 3, 5]], proof := .tail 67 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10627)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![3, 1, 4, 5, 6, 2], ![3, 0, 5, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 1, 6, 3], ![2, 0, 4, 1, 5, 3]], proof := .tail 119 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10628)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![3, 1, 4, 5, 6, 2], ![3, 0, 6, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 6, 1, 3], ![2, 0, 4, 5, 1, 3]], proof := .tail 7 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10629)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![3, 1, 4, 5, 6, 2], ![3, 0, 6, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 0, 6, 5, 1, 3], ![2, 0, 6, 4, 1, 3], ![2, 0, 5, 4, 1, 3]], proof := .tail 54 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10630)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![3, 1, 4, 6, 5, 2], ![3, 0, 6, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 0, 6, 5, 1, 3], ![2, 6, 0, 4, 1, 3], ![2, 5, 0, 4, 1, 3]], proof := .tail 95 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10631)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![3, 1, 4, 6, 5, 2], ![3, 0, 6, 5, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 0, 6, 5, 1, 3], ![6, 2, 0, 4, 1, 3], ![5, 2, 0, 4, 1, 3]], proof := .tail 95 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10632)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![3, 1, 6, 4, 5, 2], ![3, 0, 6, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 6, 0, 5, 1, 3], ![2, 6, 0, 4, 1, 3], ![2, 5, 4, 0, 1, 3]], proof := .tail 111 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10633)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![3, 1, 6, 4, 5, 2], ![3, 0, 6, 5, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 6, 0, 5, 1, 3], ![6, 2, 0, 4, 1, 3], ![5, 2, 4, 0, 1, 3]], proof := .tail 111 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10634)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![3, 1, 6, 4, 5, 2], ![3, 0, 6, 5, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 1, 0, 6, 5, 4], ![6, 2, 0, 5, 1, 3], ![6, 2, 0, 4, 1, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 62 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10635)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![3, 6, 1, 4, 5, 2], ![3, 6, 0, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 6, 0, 5, 1, 3], ![2, 6, 0, 4, 1, 3], ![2, 5, 4, 1, 0, 3]], proof := .tail 111 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10636)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![3, 6, 1, 4, 5, 2], ![3, 6, 0, 5, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 6, 0, 5, 1, 3], ![6, 2, 0, 4, 1, 3], ![5, 2, 4, 1, 0, 3]], proof := .tail 111 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10637)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![3, 6, 1, 4, 5, 2], ![3, 6, 0, 5, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 1, 0, 6, 5, 4], ![6, 2, 0, 5, 1, 3], ![6, 2, 0, 4, 1, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 62 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10638)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![6, 3, 1, 4, 5, 2], ![3, 6, 0, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 6, 0, 5, 4], ![2, 6, 0, 5, 1, 3], ![2, 6, 0, 4, 1, 3], ![2, 5, 4, 1, 3, 0]], proof := .tail 111 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10639)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![6, 3, 1, 4, 5, 2], ![3, 6, 0, 5, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 6, 0, 5, 4], ![2, 6, 0, 5, 1, 3], ![6, 2, 0, 4, 1, 3], ![5, 2, 4, 1, 3, 0]], proof := .tail 111 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10640)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 3, 1, 4, 5, 2], ![3, 6, 0, 5, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 1, 6, 0, 5, 4], ![6, 2, 0, 5, 1, 3], ![6, 2, 0, 4, 1, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 1 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10641)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![6, 3, 1, 4, 5, 2], ![6, 3, 0, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 1, 0, 5, 4], ![2, 6, 0, 5, 1, 3], ![2, 6, 0, 4, 1, 3], ![2, 5, 4, 3, 1, 0]], proof := .tail 63 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10642)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 3, 1, 4, 5, 2], ![6, 3, 0, 5, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 1, 0, 5, 4], ![2, 6, 0, 5, 1, 3], ![6, 2, 0, 4, 1, 3], ![5, 2, 4, 3, 1, 0]], proof := .tail 63 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10643)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 3, 1, 4, 5, 2], ![6, 3, 0, 5, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 1, 0, 5, 4], ![6, 2, 0, 5, 1, 3], ![6, 2, 0, 4, 1, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 63 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10644)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 3, 1, 4, 5, 2], ![6, 3, 0, 5, 4, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 1, 0, 5, 4], ![6, 2, 0, 5, 1, 3], ![6, 2, 0, 4, 1, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 24 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10645)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![3, 1, 5, 4, 2, 6], ![3, 0, 5, 4, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 1, 0, 5, 4, 6], ![2, 5, 0, 1, 3, 6], ![2, 4, 0, 1, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 164 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10646)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![3, 1, 5, 4, 2, 6], ![3, 0, 5, 4, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 1, 0, 5, 6, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 0, 1, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 3 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10647)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![3, 1, 5, 4, 2, 6], ![3, 0, 5, 4, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 1, 0, 6, 5, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 0, 1, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 169 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10648)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![3, 1, 5, 4, 2, 6], ![3, 0, 5, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 5, 4, 6], ![2, 5, 0, 1, 3, 6], ![2, 4, 0, 1, 3, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 45 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10649)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![3, 1, 5, 4, 2, 6], ![3, 0, 5, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 5, 6, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 0, 1, 3, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 58 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10650)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![3, 1, 5, 4, 2, 6], ![3, 0, 5, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 6, 5, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 0, 1, 6, 3], ![0, 2, 1, 4, 5, 3]], proof := .tail 160 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10651)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![3, 1, 5, 4, 2, 6], ![3, 0, 5, 6, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 5, 6, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 1, 3, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 136 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10652)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![3, 1, 5, 4, 2, 6], ![3, 0, 5, 6, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 6, 5, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 1, 6, 3], ![0, 2, 4, 1, 5, 3]], proof := .tail 136 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10653)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![3, 1, 5, 4, 2, 6], ![3, 0, 6, 5, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 6, 5, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 6, 1, 3], ![0, 2, 4, 5, 1, 3]], proof := .tail 130 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10654)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![3, 1, 5, 4, 6, 2], ![3, 0, 5, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 5, 4, 6], ![2, 5, 0, 1, 3, 6], ![2, 4, 0, 1, 3, 6], ![2, 0, 1, 3, 4, 5]], proof := .low (![96, 132, 100, 163, 98, 16, 29, 104, 5, 137, 2, 28, 53, 12, 75, 127, 32, 113, 68, 77, 27, 90, 94, 49, 142, 25, 10, 141]) }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10655)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![3, 1, 5, 4, 6, 2], ![3, 0, 5, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 5, 6, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 0, 1, 3, 6], ![2, 0, 1, 4, 3, 5]], proof := .tail 58 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10656)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![3, 1, 5, 4, 6, 2], ![3, 0, 5, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 0, 1, 6, 3], ![2, 0, 1, 4, 5, 3]], proof := .tail 169 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10657)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![3, 1, 5, 4, 6, 2], ![3, 0, 5, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 5, 6, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 1, 3, 6], ![2, 0, 4, 1, 3, 5]], proof := .tail 136 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10658)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![3, 1, 5, 4, 6, 2], ![3, 0, 5, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 1, 6, 3], ![2, 0, 4, 1, 5, 3]], proof := .tail 136 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10659)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![3, 1, 5, 4, 6, 2], ![3, 0, 6, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 6, 1, 3], ![2, 0, 4, 5, 1, 3]], proof := .tail 130 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10660)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![3, 1, 5, 6, 4, 2], ![3, 0, 5, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 5, 6, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 0, 1, 3, 6], ![2, 4, 0, 1, 3, 5]], proof := .low (![80, 31, 100, 69, 135, 42, 29, 93, 5, 152, 154, 114, 53, 60, 57, 55, 13, 113, 21, 84, 86, 47, 23, 59, 79, 109, 131, 150]) }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10661)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![3, 1, 5, 6, 4, 2], ![3, 0, 5, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 0, 1, 6, 3], ![2, 4, 0, 1, 5, 3]], proof := .tail 40 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10662)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![3, 1, 5, 6, 4, 2], ![3, 0, 6, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 0, 6, 1, 3], ![2, 4, 0, 5, 1, 3]], proof := .tail 125 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10663)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![3, 1, 6, 5, 4, 2], ![3, 0, 6, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 6, 0, 1, 3], ![2, 4, 5, 0, 1, 3]], proof := .tail 17 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10664)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![3, 1, 6, 5, 4, 2], ![3, 0, 6, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 6, 5, 0, 1, 3], ![2, 6, 4, 0, 1, 3], ![2, 5, 4, 0, 1, 3]], proof := .tail 170 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10665)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![3, 1, 6, 5, 4, 2], ![3, 0, 6, 5, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 6, 5, 0, 1, 3], ![6, 2, 4, 0, 1, 3], ![5, 2, 4, 0, 1, 3]], proof := .low (![140, 91, 35, 120, 157, 102, 29, 143, 106, 134, 19, 9, 53, 88, 36, 71, 13, 113, 89, 124, 70, 144, 151, 122, 74, 18, 39, 158]) }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10666)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![3, 1, 6, 5, 4, 2], ![3, 0, 6, 5, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 1, 0, 6, 5, 4], ![6, 2, 5, 0, 1, 3], ![6, 2, 4, 0, 1, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 168 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10667)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![3, 6, 1, 5, 4, 2], ![3, 6, 0, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 6, 0, 1, 3], ![2, 4, 5, 1, 0, 3]], proof := .tail 82 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10668)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![3, 6, 1, 5, 4, 2], ![3, 6, 0, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 6, 5, 0, 1, 3], ![2, 6, 4, 0, 1, 3], ![2, 5, 4, 1, 0, 3]], proof := .tail 110 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10669)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![3, 6, 1, 5, 4, 2], ![3, 6, 0, 5, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 6, 5, 0, 1, 3], ![6, 2, 4, 0, 1, 3], ![5, 2, 4, 1, 0, 3]], proof := .tail 110 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10670)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![3, 6, 1, 5, 4, 2], ![3, 6, 0, 5, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 1, 0, 6, 5, 4], ![6, 2, 5, 0, 1, 3], ![6, 2, 4, 0, 1, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 168 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10671)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![6, 3, 1, 5, 4, 2], ![3, 6, 0, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 6, 0, 5, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 6, 0, 1, 3], ![2, 4, 5, 1, 3, 0]], proof := .tail 112 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10672)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![6, 3, 1, 5, 4, 2], ![3, 6, 0, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 6, 0, 5, 4], ![2, 6, 5, 0, 1, 3], ![2, 6, 4, 0, 1, 3], ![2, 5, 4, 1, 3, 0]], proof := .tail 87 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10673)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![6, 3, 1, 5, 4, 2], ![3, 6, 0, 5, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 6, 0, 5, 4], ![2, 6, 5, 0, 1, 3], ![6, 2, 4, 0, 1, 3], ![5, 2, 4, 1, 3, 0]], proof := .tail 87 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10674)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![6, 3, 1, 5, 4, 2], ![3, 6, 0, 5, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 1, 6, 0, 5, 4], ![6, 2, 5, 0, 1, 3], ![6, 2, 4, 0, 1, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 168 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10675)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![6, 3, 1, 5, 4, 2], ![6, 3, 0, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 1, 0, 5, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 6, 0, 1, 3], ![2, 4, 5, 3, 1, 0]], proof := .tail 97 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10676)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![6, 3, 1, 5, 4, 2], ![6, 3, 0, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 1, 0, 5, 4], ![2, 6, 5, 0, 1, 3], ![2, 6, 4, 0, 1, 3], ![2, 5, 4, 3, 1, 0]], proof := .tail 63 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10677)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![6, 3, 1, 5, 4, 2], ![6, 3, 0, 5, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 1, 0, 5, 4], ![2, 6, 5, 0, 1, 3], ![6, 2, 4, 0, 1, 3], ![5, 2, 4, 3, 1, 0]], proof := .tail 63 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10678)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![6, 3, 1, 5, 4, 2], ![6, 3, 0, 5, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 1, 0, 5, 4], ![6, 2, 5, 0, 1, 3], ![6, 2, 4, 0, 1, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 63 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10679)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![6, 3, 1, 5, 4, 2], ![6, 3, 0, 5, 4, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 1, 0, 5, 4], ![6, 2, 5, 0, 1, 3], ![6, 2, 4, 0, 1, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 168 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10680)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![3, 1, 5, 4, 2, 6], ![3, 0, 5, 4, 2, 6], ![3, 5, 4, 0, 1, 6], ![2, 1, 0, 5, 4, 6], ![5, 2, 0, 1, 3, 6], ![4, 2, 0, 1, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 148 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10681)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![3, 1, 5, 4, 2, 6], ![3, 0, 5, 4, 2, 6], ![3, 5, 4, 0, 1, 6], ![2, 1, 0, 5, 6, 4], ![5, 2, 0, 1, 6, 3], ![4, 2, 0, 1, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 145 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10682)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![3, 1, 5, 4, 2, 6], ![3, 0, 5, 4, 2, 6], ![3, 5, 4, 0, 1, 6], ![2, 1, 0, 6, 5, 4], ![5, 2, 0, 1, 6, 3], ![4, 2, 0, 1, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 107 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10683)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![3, 1, 5, 4, 2, 6], ![3, 0, 5, 4, 6, 2], ![3, 5, 4, 0, 6, 1], ![2, 1, 0, 5, 4, 6], ![5, 2, 0, 1, 3, 6], ![4, 2, 0, 1, 3, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 0 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10684)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![3, 1, 5, 4, 2, 6], ![3, 0, 5, 4, 6, 2], ![3, 5, 4, 0, 6, 1], ![2, 1, 0, 5, 6, 4], ![5, 2, 0, 1, 6, 3], ![4, 2, 0, 1, 3, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 101 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10685)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![3, 1, 5, 4, 2, 6], ![3, 0, 5, 4, 6, 2], ![3, 5, 4, 0, 6, 1], ![2, 1, 0, 6, 5, 4], ![5, 2, 0, 1, 6, 3], ![4, 2, 0, 1, 6, 3], ![0, 2, 1, 4, 5, 3]], proof := .tail 34 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10686)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![3, 1, 5, 4, 2, 6], ![3, 0, 5, 6, 4, 2], ![3, 5, 4, 0, 6, 1], ![2, 1, 0, 5, 6, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 1, 3, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 6 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10687)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![3, 1, 5, 4, 2, 6], ![3, 0, 5, 6, 4, 2], ![3, 5, 4, 0, 6, 1], ![2, 1, 0, 6, 5, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 1, 6, 3], ![0, 2, 4, 1, 5, 3]], proof := .tail 34 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10688)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![3, 1, 5, 4, 2, 6], ![3, 0, 6, 5, 4, 2], ![3, 5, 4, 0, 6, 1], ![2, 1, 0, 6, 5, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 6, 1, 3], ![0, 2, 4, 5, 1, 3]], proof := .tail 37 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10689)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![3, 1, 5, 4, 6, 2], ![3, 0, 5, 4, 6, 2], ![3, 5, 4, 6, 0, 1], ![2, 1, 0, 5, 4, 6], ![5, 2, 0, 1, 3, 6], ![4, 2, 0, 1, 3, 6], ![2, 0, 1, 3, 4, 5]], proof := .low (![96, 132, 100, 163, 38, 56, 29, 104, 5, 137, 51, 28, 53, 12, 75, 127, 32, 113, 68, 77, 27, 90, 94, 49, 64, 33, 139, 4]) }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10690)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![3, 1, 5, 4, 6, 2], ![3, 0, 5, 4, 6, 2], ![3, 5, 4, 6, 0, 1], ![2, 1, 0, 5, 6, 4], ![5, 2, 0, 1, 6, 3], ![4, 2, 0, 1, 3, 6], ![2, 0, 1, 4, 3, 5]], proof := .tail 147 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10691)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![3, 1, 5, 4, 6, 2], ![3, 0, 5, 4, 6, 2], ![3, 5, 4, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![5, 2, 0, 1, 6, 3], ![4, 2, 0, 1, 6, 3], ![2, 0, 1, 4, 5, 3]], proof := .tail 15 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10692)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![3, 1, 5, 4, 6, 2], ![3, 0, 5, 6, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 1, 0, 5, 6, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 1, 3, 6], ![2, 0, 4, 1, 3, 5]], proof := .tail 146 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10693)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![3, 1, 5, 4, 6, 2], ![3, 0, 5, 6, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 1, 6, 3], ![2, 0, 4, 1, 5, 3]], proof := .tail 34 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10694)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![3, 1, 5, 4, 6, 2], ![3, 0, 6, 5, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 6, 1, 3], ![2, 0, 4, 5, 1, 3]], proof := .tail 37 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10695)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![3, 1, 5, 6, 4, 2], ![3, 0, 5, 6, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 1, 0, 5, 6, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 0, 1, 3, 6], ![2, 4, 0, 1, 3, 5]], proof := .tail 72 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10696)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![3, 1, 5, 6, 4, 2], ![3, 0, 5, 6, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 0, 1, 6, 3], ![2, 4, 0, 1, 5, 3]], proof := .tail 20 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10697)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![3, 1, 5, 6, 4, 2], ![3, 0, 6, 5, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 0, 6, 1, 3], ![2, 4, 0, 5, 1, 3]], proof := .tail 37 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10698)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![3, 1, 6, 5, 4, 2], ![3, 0, 6, 5, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 6, 0, 1, 3], ![2, 4, 5, 0, 1, 3]], proof := .tail 129 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10699)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![3, 1, 5, 6, 4, 2], ![3, 0, 5, 6, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 1, 0, 5, 6, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 0, 1, 3, 6], ![4, 2, 0, 1, 3, 5]], proof := .low (![80, 31, 100, 69, 135, 123, 29, 93, 5, 152, 154, 50, 53, 60, 57, 55, 13, 113, 21, 84, 86, 47, 23, 59, 78, 109, 116, 8]) }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10700)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![3, 1, 5, 6, 4, 2], ![3, 0, 5, 6, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 1, 0, 6, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 0, 1, 6, 3], ![4, 2, 0, 1, 5, 3]], proof := .tail 41 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10701)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![3, 1, 5, 6, 4, 2], ![3, 0, 6, 5, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 1, 0, 6, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 0, 6, 1, 3], ![4, 2, 0, 5, 1, 3]], proof := .tail 105 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10702)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![3, 1, 6, 5, 4, 2], ![3, 0, 6, 5, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 1, 0, 6, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 6, 0, 1, 3], ![4, 2, 5, 0, 1, 3]], proof := .low (![140, 91, 35, 120, 26, 61, 29, 143, 106, 134, 52, 149, 53, 88, 36, 71, 13, 113, 89, 124, 70, 144, 151, 122, 138, 11, 48, 108]) }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10703)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![3, 1, 6, 5, 4, 2], ![3, 0, 6, 5, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 1, 0, 6, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 6, 2, 0, 1, 3], ![4, 5, 2, 0, 1, 3]], proof := .tail 161 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10704)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![3, 1, 6, 5, 4, 2], ![3, 0, 6, 5, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 1, 0, 6, 5, 4], ![6, 5, 2, 0, 1, 3], ![6, 4, 2, 0, 1, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 83 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10705)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![3, 6, 1, 5, 4, 2], ![3, 6, 0, 5, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 6, 0, 1, 3], ![2, 4, 5, 1, 0, 3]], proof := .tail 115 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10706)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![3, 6, 1, 5, 4, 2], ![3, 6, 0, 5, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 1, 0, 6, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 6, 0, 1, 3], ![4, 2, 5, 1, 0, 3]], proof := .tail 115 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10707)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![3, 6, 1, 5, 4, 2], ![3, 6, 0, 5, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 1, 0, 6, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 6, 2, 0, 1, 3], ![4, 5, 2, 1, 0, 3]], proof := .tail 66 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10708)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![3, 6, 1, 5, 4, 2], ![3, 6, 0, 5, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 1, 0, 6, 5, 4], ![6, 5, 2, 0, 1, 3], ![6, 4, 2, 0, 1, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 83 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10709)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![6, 3, 1, 5, 4, 2], ![3, 6, 0, 5, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 1, 6, 0, 5, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 6, 0, 1, 3], ![2, 4, 5, 1, 3, 0]], proof := .tail 44 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10710)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![6, 3, 1, 5, 4, 2], ![3, 6, 0, 5, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 1, 6, 0, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 6, 0, 1, 3], ![4, 2, 5, 1, 3, 0]], proof := .tail 103 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10711)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![6, 3, 1, 5, 4, 2], ![3, 6, 0, 5, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 1, 6, 0, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 6, 2, 0, 1, 3], ![4, 5, 2, 1, 3, 0]], proof := .tail 126 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10712)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![6, 3, 1, 5, 4, 2], ![3, 6, 0, 5, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 1, 6, 0, 5, 4], ![6, 5, 2, 0, 1, 3], ![6, 4, 2, 0, 1, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 156 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10713)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![6, 3, 1, 5, 4, 2], ![6, 3, 0, 5, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 6, 1, 0, 5, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 6, 0, 1, 3], ![2, 4, 5, 3, 1, 0]], proof := .tail 166 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10714)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![6, 3, 1, 5, 4, 2], ![6, 3, 0, 5, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 6, 1, 0, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 6, 0, 1, 3], ![4, 2, 5, 3, 1, 0]], proof := .tail 166 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10715)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![6, 3, 1, 5, 4, 2], ![6, 3, 0, 5, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 6, 1, 0, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 6, 2, 0, 1, 3], ![4, 5, 2, 3, 1, 0]], proof := .tail 159 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10716)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![6, 3, 1, 5, 4, 2], ![6, 3, 0, 5, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 6, 1, 0, 5, 4], ![6, 5, 2, 0, 1, 3], ![6, 4, 2, 0, 1, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 63 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10717)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![6, 3, 1, 5, 4, 2], ![6, 3, 0, 5, 4, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 1, 0, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 6, 2, 0, 1, 3], ![4, 5, 3, 2, 1, 0]], proof := .tail 14 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10718)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 3, 1, 5, 4, 2], ![6, 3, 0, 5, 4, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 1, 0, 5, 4], ![6, 5, 2, 0, 1, 3], ![6, 4, 2, 0, 1, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 30 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10719)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![3, 5, 1, 4, 2, 6], ![3, 5, 0, 4, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 1, 0, 5, 4, 6], ![2, 5, 0, 1, 3, 6], ![2, 4, 1, 0, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 65 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10720)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![3, 5, 1, 4, 2, 6], ![3, 5, 0, 4, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 1, 0, 5, 6, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 1, 0, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 121 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10721)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![3, 5, 1, 4, 2, 6], ![3, 5, 0, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 5, 4, 6], ![2, 5, 0, 1, 3, 6], ![2, 4, 1, 0, 3, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 167 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10722)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![3, 5, 1, 4, 2, 6], ![3, 5, 0, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 5, 6, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 1, 0, 3, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 121 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10723)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![3, 5, 1, 4, 2, 6], ![3, 5, 0, 6, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 5, 6, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 1, 0, 3, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 128 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10724)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![3, 5, 1, 4, 6, 2], ![3, 5, 0, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 5, 4, 6], ![2, 5, 0, 1, 3, 6], ![2, 4, 1, 0, 3, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 46 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10725)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![3, 5, 1, 4, 6, 2], ![3, 5, 0, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 5, 6, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 1, 0, 3, 6], ![2, 0, 1, 4, 3, 5]], proof := .tail 121 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10726)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![3, 5, 1, 4, 6, 2], ![3, 5, 0, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 5, 6, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 1, 0, 3, 6], ![2, 0, 4, 1, 3, 5]], proof := .tail 128 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10727)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![3, 5, 1, 6, 4, 2], ![3, 5, 0, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 5, 6, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 1, 0, 3, 6], ![2, 4, 0, 1, 3, 5]], proof := .tail 128 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10728)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![3, 5, 1, 4, 2, 6], ![3, 5, 0, 4, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 1, 0, 6, 5, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 1, 0, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 43 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10729)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![3, 5, 1, 4, 2, 6], ![3, 5, 0, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 6, 5, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 1, 0, 6, 3], ![0, 2, 1, 4, 5, 3]], proof := .tail 43 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10730)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![3, 5, 1, 4, 2, 6], ![3, 5, 0, 6, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 6, 5, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 1, 0, 6, 3], ![0, 2, 4, 1, 5, 3]], proof := .tail 128 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10731)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![3, 5, 1, 4, 6, 2], ![3, 5, 0, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 1, 0, 6, 3], ![2, 0, 1, 4, 5, 3]], proof := .tail 43 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10732)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![3, 5, 1, 4, 6, 2], ![3, 5, 0, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 1, 0, 6, 3], ![2, 0, 4, 1, 5, 3]], proof := .tail 128 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10733)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![3, 5, 1, 6, 4, 2], ![3, 5, 0, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 1, 0, 6, 3], ![2, 4, 0, 1, 5, 3]], proof := .tail 155 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10734)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![3, 5, 6, 1, 4, 2], ![3, 5, 6, 0, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 5, 6, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 1, 0, 3, 6], ![2, 4, 1, 0, 3, 5]], proof := .tail 76 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10735)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![3, 5, 6, 1, 4, 2], ![3, 5, 6, 0, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 1, 0, 6, 3], ![2, 4, 1, 0, 5, 3]], proof := .tail 76 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10736)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![3, 6, 5, 1, 4, 2], ![3, 5, 6, 0, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 1, 6, 0, 3], ![2, 4, 1, 5, 0, 3]], proof := .tail 133 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10737)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![3, 6, 5, 1, 4, 2], ![3, 6, 5, 0, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 6, 1, 0, 3], ![2, 4, 5, 1, 0, 3]], proof := .tail 118 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10738)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![3, 6, 5, 1, 4, 2], ![3, 6, 5, 0, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 6, 5, 0, 1, 3], ![2, 6, 4, 1, 0, 3], ![2, 5, 4, 1, 0, 3]], proof := .tail 81 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10739)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![3, 6, 5, 1, 4, 2], ![3, 6, 5, 0, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 6, 5, 0, 1, 3], ![6, 2, 4, 1, 0, 3], ![5, 2, 4, 1, 0, 3]], proof := .tail 165 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10740)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 3, 5, 1, 4, 2], ![3, 5, 6, 0, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 6, 0, 5, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 1, 6, 0, 3], ![2, 4, 1, 5, 3, 0]], proof := .tail 162 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10741)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 3, 5, 1, 4, 2], ![3, 6, 5, 0, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 6, 0, 5, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 6, 1, 0, 3], ![2, 4, 5, 1, 3, 0]], proof := .tail 118 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10742)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 3, 5, 1, 4, 2], ![3, 6, 5, 0, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 6, 0, 5, 4], ![2, 6, 5, 0, 1, 3], ![2, 6, 4, 1, 0, 3], ![2, 5, 4, 1, 3, 0]], proof := .tail 81 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10743)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 3, 5, 1, 4, 2], ![3, 6, 5, 0, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 6, 0, 5, 4], ![2, 6, 5, 0, 1, 3], ![6, 2, 4, 1, 0, 3], ![5, 2, 4, 1, 3, 0]], proof := .tail 117 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10744)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 3, 5, 1, 4, 2], ![6, 3, 5, 0, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 1, 0, 5, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 6, 1, 0, 3], ![2, 4, 5, 3, 1, 0]], proof := .tail 22 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10745)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![6, 3, 5, 1, 4, 2], ![6, 3, 5, 0, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 1, 0, 5, 4], ![2, 6, 5, 0, 1, 3], ![2, 6, 4, 1, 0, 3], ![2, 5, 4, 3, 1, 0]], proof := .tail 73 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10746)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 3, 5, 1, 4, 2], ![6, 3, 5, 0, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 1, 0, 5, 4], ![2, 6, 5, 0, 1, 3], ![6, 2, 4, 1, 0, 3], ![5, 2, 4, 3, 1, 0]], proof := .tail 73 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10747)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![3, 6, 5, 1, 4, 2], ![3, 6, 5, 0, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 1, 0, 6, 5, 4], ![6, 2, 5, 0, 1, 3], ![6, 2, 4, 1, 0, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 153 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10748)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 3, 5, 1, 4, 2], ![3, 6, 5, 0, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 1, 6, 0, 5, 4], ![6, 2, 5, 0, 1, 3], ![6, 2, 4, 1, 0, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 153 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10749)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 3, 5, 1, 4, 2], ![6, 3, 5, 0, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 1, 0, 5, 4], ![6, 2, 5, 0, 1, 3], ![6, 2, 4, 1, 0, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 153 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10750)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 3, 5, 1, 4, 2], ![6, 3, 5, 0, 4, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 1, 0, 5, 4], ![6, 2, 5, 0, 1, 3], ![6, 2, 4, 1, 0, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 153 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10751)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (10624 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 10624 ≤ id.val) (hhigh : id.val < 10752) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 10624)) = true := by
  let j : Fin 128 := ⟨id.val - 10624, by omega⟩
  have hsum : 10624 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (10624 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard083
