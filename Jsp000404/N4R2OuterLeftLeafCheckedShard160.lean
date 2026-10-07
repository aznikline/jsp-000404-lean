import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard160
open N4R2OuterLeftReplay

-- Cycle fingerprint 017594b4098680128e56d42e1abe4ddcd15542845cef8927851a33221ba05b12.
def localCycle00000 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 4, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 2 0, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 0310ff91b2389153a1c2728f6df594b74a2179188755e0388c2847cc91b9632b.
def localCycle00001 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint 03c47046f7e05877a51d898810632daeffdc30b21f12253f6db94af585c67aa7.
def localCycle00002 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 2]
    constant := ![-2, 3, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 05bed85b0c06f6059c1232f6953c9e19e8b01977ea6d0abc6c9ae355a16da4d5.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 0825efae243a5ce07249c4570bf75c3f422d3964e6ff332c8bbb08fed4a160f1.
def localCycle00004 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -3, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 2, .triangle 24 1, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 16c7c021752a604ddeb84c9aee2f25f310ad0c7ca491f48aee55faec17e4ccbb.
def localCycle00005 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 2, .triangle 24 1, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 203a994fa2af6422cde7c3166de3e24eb8c2c5ff36174a97c692b8735833e32a.
def localCycle00006 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 6, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 2, .triangle 6 1, .triangle 8 0, .triangle 30 1, .triangle 17 0, .corridorLower 1 2]

-- Cycle fingerprint 23df9b7cbb144863b511d26187f5a3fc90330b252c853a42f8de39ef10a8f776.
def localCycle00007 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 6 1, .triangle 5 0, .triangle 15 2, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 287025c70e676c8fcfd2c3549b146381d8f3f4fb54f66e8204783719981f452d.
def localCycle00008 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3]
    constant := ![-1, 0, -1, 0, 0, 0, 4, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 27 0, .triangle 33 1, .triangle 34 0, .gapLower 4 1, .gapLower 1 2, .gapLower 3 0, .gapLower 3 6, .triangle 9 0, .triangle 10 0, .triangle 26 0]

-- Cycle fingerprint 2badcad67f7e18e8fac581b6e2643fcafd903b6a1f144e588b9f964ea714b165.
def localCycle00009 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -1, 0, 0, -2, -2, -1, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 6 0, .triangle 8 0, .triangle 18 2, .triangle 24 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 3212106df51a045667c03ab9ded10be0715567478ae459252ad45053e6bbfbb2.
def localCycle00010 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 349eeb80eb2ec711237b9448f809234c5b89e081d08e767203ce3ba4c2c15e61.
def localCycle00011 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 26 1, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint 3b3967152d16adc3ccf8065f68aef5be3d0ef06bb66b32c1eaaecf6b47880b57.
def localCycle00012 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 3ef584eaa827a32bbe31e0f50775c0078da7617e6e5c9e9fa8bf8f93a46a657b.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Cycle fingerprint 3fd7fc7805927e3723fef41a5ba2cf664e7fa062686cdb4f2d5e18ec8f75ac32.
def localCycle00014 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 27 1, .triangle 26 0, .triangle 31 1, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 41a3ef65db35db77d1c07a1720bb072a66b6555cfad85919fcadbb6261169fc3.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 5 0, .triangle 15 2, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 4229a1f996d6bdd3bb0aac43090dd88808ce5f23bc4ad2081f0139b4d6f06522.
def localCycle00016 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 4294fda3c0a392ec507bb69b5941111e91aaef88a573b206c9fdef1d6f955ef0.
def localCycle00017 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 10 1, .triangle 11 0, .triangle 27 2, .triangle 29 1, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 44375e4f4f104d8e6069ee562b8660ddfa30a1cdddbe8d00289e5987f7e5f5c8.
def localCycle00018 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 47bb6406134c367dfa1b75926ed33ca81960691109c283f6e649b50cd9e4dad9.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 33 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 4855dba80057abd9e8f8f888ecb584c205463b12b3700abbb8266e8035dd4d5a.
def localCycle00020 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 30 2, .triangle 29 1, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 48b422755bef84bfeb4bd7c3de8e84172cdca26f9e6f033ca410b4d2908ed666.
def localCycle00021 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 50cfa29a05b6bf308b26f86f66b14b3c469dde02f78579de797f819682b93bac.
def localCycle00022 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 6 1, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 50d4cc64a5e03611408dcc53f7cfcbb037962e620bc064137cfef40e799c29c7.
def localCycle00023 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 26 1, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 51b14c48b48dbb846984c5a31ed77dbad6e80a6fad99d7bc728785777f61b82d.
def localCycle00024 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 51fd63eb4631fa23c07fe72e79bacb7db12283f49e13e3735b377bf8344ee805.
def localCycle00025 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 26 0, .triangle 31 1, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 5a28d79874061aa88c97bb8cfb69957fd192b0ba3bcd40830a8ac0da13553ac0.
def localCycle00026 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 6, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 6, .corridorUpper 0 1]

-- Cycle fingerprint 5e8c986866408ce789bedb4d5bec27d3162f4641c6bff73ced8576fcd85e8bc8.
def localCycle00027 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 27 0, .triangle 32 1, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 63d1a11b3e14d306fb019df825ba4075bacef01d8a858373e68dd1dd5b69f53d.
def localCycle00028 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 2, .triangle 21 1, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 6a2fdebb1298fad34c72d0d03b457067f8394478286d73509729428fcb3e85db.
def localCycle00029 : Cycle where
  length := 10
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6]
    constant := ![-1, 0, 0, 3, 0, -1, -1, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 3, .gapLower 4 0, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 26 0, .triangle 31 1, .triangle 34 0]

-- Cycle fingerprint 70c69c2420e8da89309b10a5eb58dcce15870f0a24c46772b865139f9fcd1004.
def localCycle00030 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-1, 4, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 5, .gapLower 1 6, .triangle 2 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 70dd042d2a1ce7b56cc11c9d180b0ffd4ca9fb3bbf67e99859a2b44827c65f37.
def localCycle00031 : Cycle where
  length := 12
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4]
    constant := ![0, -1, 0, 0, 3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 5 0, .triangle 26 0, .triangle 31 1, .triangle 22 0]

-- Cycle fingerprint 735e73e9ae428bf25da6f1ad5a6935ca56aab1e17e7b6b5d028dba34c897a225.
def localCycle00032 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 2, .triangle 22 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 7776fff64628298833319306871b732fd65d54673336fb0cdb29e4260f56eaf2.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 29 1, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 78207b76866eb1511b612bcc8df35730d8cb74cf7ffe672e584d58da8531af2a.
def localCycle00034 : Cycle where
  length := 14
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5]
    constant := ![-1, 0, -1, 3, 0, -1, -1, -1, -1, 3, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 20 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 26 0]

-- Cycle fingerprint 79d4ef63562fd57c4f4fe5f694bd21198cbdbfee507efb121febd86588f9acc4.
def localCycle00035 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 26 0, .triangle 31 1, .triangle 22 0, .triangle 23 0, .corridorLower 4 6]

-- Cycle fingerprint 833afcee5456b98b03b68a3c5748bca445172caa42997b08d7ffe47752cbbd6d.
def localCycle00036 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 26 1, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 84ef82ef5e5685e82395ce3c7aca527e6f7c4bf29d87bc5df7f1dcaa0eb2a61f.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 2 5]
    constant := ![-1, -3, 0, 0, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 17 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 30 1]

-- Cycle fingerprint 850b080f74e6663c9813f1ac2a580612552a62757567df1b223eb8710b39617c.
def localCycle00038 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 15 2, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 8663ebb208a146483daa4688a5e5ef157bc5a83ca7e60c377e87cea43452f0cb.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 4 5, .theta 4, .distance 3 4]
    constant := ![0, -1, -1, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 2, .gapLower 1 3, .triangle 22 1, .gapLower 4 0, .corridorUpper 3 4]

-- Cycle fingerprint 88b6a67b9dc9568cb1e56693f85d09687c5067176348b4c1b04e469a25570b50.
def localCycle00040 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, 0, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 23 2, .triangle 24 1, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint 8d25b7d437972549039f24a3e4a2e091ceec492c1d4b7da1cbaa094bd3c8b09b.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6]
    constant := ![0, -2, 0, -1, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, true, false, false] }
  origin := ![.triangle 18 2, .gapLower 1 3, .triangle 22 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0]

-- Cycle fingerprint 8f1064f8d3be493460a47f0f18db1b9ab1c84bf58e425666a1a11c542c48089e.
def localCycle00042 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint 8f5f4fd5a1c3b5cd11d85862d6dd4e681643c53bd79ffbcab403a944f62a70a5.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 15 2, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 9097b3bf67c2f88e519bbefb6edef9260d469a9caf8692a003d6e0afa6d1842e.
def localCycle00044 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 26 1, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 91211656b7c862126b6a2f229fedaf81b758278ca61f65137a0979ae1b50a2dc.
def localCycle00045 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 2 5, .distance 2 3]
    constant := ![-1, -1, 2, -2, -1, 0, -1, 3, 0, -1, -1, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, false, false, true, true] }
  origin := ![.triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 23 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 30 1, .triangle 26 1]

-- Cycle fingerprint 9125ea716f851a477f92875dd2ba963e6378c2a52a221fa00de204d2bba8deed.
def localCycle00046 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 2, .triangle 20 1, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 91f19e891df9b30423ed99787ef24dc598dfc6ab416139b822e3b8b5f856f27f.
def localCycle00047 : Cycle where
  length := 14
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4]
    constant := ![0, -1, 0, -1, 3, 0, -1, -1, -1, -1, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 3, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 0]

-- Cycle fingerprint 9606a3f739b32997e40e2ba5c5451488ac679949851c3e8c1cb77981387b7f78.
def localCycle00048 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 26 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 99190ef61ee87d7153d71afc6a17bee7c9c536e48b39da5f14d546e19d44ecf1.
def localCycle00049 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 9d457ad25b18da9ca71052e4abf3082032da758f59fe9d049860de7fc7f37ce2.
def localCycle00050 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 4 5, .theta 4, .distance 3 4]
    constant := ![0, -1, -1, 0, -3, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 2, .gapLower 1 3, .triangle 22 1, .corridorLower 4 5, .corridorUpper 3 4]

-- Cycle fingerprint 9e602e2b21fa8e74faa1dfee7c49b7b1c7163e813b35ec1b658db6dee60b3223.
def localCycle00051 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint a04cde79f6e0dcaa6f3495ac8dce1a9d275d1487b997deafdfcc8713d4c8eef2.
def localCycle00052 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 10 1, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint a0f77d97522bcfba30b3d1ad9a69141272c810c72d804486c099cf30c0190207.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .gapLower 4 1, .gapLower 4 0]

-- Cycle fingerprint a12fb9db1f3eeff475c54506c6b51bab254c4b37ca6371f6d6dc5a89382b4d60.
def localCycle00054 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3]
    constant := ![-1, 0, 0, -1, 0, 0, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0]

-- Cycle fingerprint a208c0ebb82abc3c696d961a42495e8971a05fa8097f9b9dfec7ef3bfe1f8a79.
def localCycle00055 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 4, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 2 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint a41fa6fc9bd002eb1bab8e9abb6545bf907c49f233684888965d0baf1c586f92.
def localCycle00056 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 2, .triangle 20 1, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint a5d041d1370bb906360a5f835087a60ecd5876c9d9b40ebc403ed6599f11f477.
def localCycle00057 : Cycle where
  length := 15
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, 3, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 8 0, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint a7de5df3bb3a2bb1b6879507ec9ef9eb8e97482fb48b37e88eacaaa69e5f4cc2.
def localCycle00058 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint aa7839fb9dc814bc168e5d66ad0c4cc94bc00d0ecbf332c4f559b40ad4692a7f.
def localCycle00059 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3]
    constant := ![-1, -1, 0, -1, 0, 0, 3, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 26 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 5 0]

-- Cycle fingerprint aab5e6660832c7d8070d0087c27ee8080dce542ff77f20efcd1d982b119b1d5e.
def localCycle00060 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 29 1, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint ac52088406b17996a5bdb5804ef4a8727316056eec1de7ab4052b6aa4f83a81b.
def localCycle00061 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 2, .distance 2 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 3 1, .gapLower 1 1, .gapUpper 2 1]

-- Cycle fingerprint b154840ab00b09208aaf0c815b5c1239039380ecc605ca4d2f8b8afbfbe1f94a.
def localCycle00062 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 6, .distance 2 5, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6]
    constant := ![0, -1, -2, 3, -2, -1, 0, -1, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, false, true, false, false] }
  origin := ![.triangle 30 1, .triangle 17 0, .gapLower 1 0, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0]

-- Cycle fingerprint b40327aaa0c94857cd7506de91be0817854a49ba9e7a9c45015253d541f2c796.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 6, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6]
    constant := ![0, -1, -2, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 30 1, .triangle 17 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0]

-- Cycle fingerprint b6b5d76555c5141e928a2c48cbeb6658af7858e03f0934c3285eb024780dcb87.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint b76f5970a5e7e0095222ce1816bfaa2ab82658f3249589feab8013c5aa092000.
def localCycle00065 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, -1, 0, 0, 0, -2, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, true, true, true, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 2, .triangle 24 1, .triangle 20 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint beb12b91ec7e2544eb5f3bfb43378bdf4fa9cc4272f359d2f7a49bd342f5f1b8.
def localCycle00066 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5]
    constant := ![0, -1, -1, 0, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 28 1, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .gapLower 4 0, .corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2]

-- Cycle fingerprint bfe611c9f883a226392bce357f251dac65404788b0c1af9c0579ad0d828afc43.
def localCycle00067 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 2, .triangle 11 1, .triangle 10 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint c08ecc5d8e2bc61ff627ee0628cf50fef1baa06c171ade958018c2059751c715.
def localCycle00068 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2]
    constant := ![-1, 2, 0, 0, -1, 0, 0, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, true, false] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 2 2, .triangle 6 1, .triangle 8 0, .triangle 18 2, .triangle 24 1, .triangle 20 1, .gapLower 1 1]

-- Cycle fingerprint c1a6c560baf98a13faf9a3136cd44b848bdce5867c67ac5ce1da63da78d813d6.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint c35cb4a0305725894443cd60971bb30c0e2a87e62f9254a2425aebb993a9b0b1.
def localCycle00070 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 5, .distance 1 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 30 0, .triangle 17 2, .triangle 22 1, .corridorLower 4 5]

-- Cycle fingerprint c40532031f7363980370362ef642a9848643205d623c6518fb87c6311ac8f270.
def localCycle00071 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 27 0, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint c55cdfe2403613308600deaf75f6517b3e5e972797fb4f295adc5be4ea85375f.
def localCycle00072 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint c82196962e58d7c4e8564dc9ba61bf0195644410e98433a770a1ec47fb670a77.
def localCycle00073 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6]
    constant := ![0, -2, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 2]

-- Cycle fingerprint c8ff02093234d8a4664ba0dceb2eb7997a2e05d0d4cf6c73da535468db64e1fc.
def localCycle00074 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint ce19faa6dc5a6132fd57f439170a6199768b2afea48048bc9a52b3c232028e4d.
def localCycle00075 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 6, .distance 4 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 2, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint cf9e15ad8ff4da415e336caa151b57234022b1b5b0ce2bf1e299b11a23ec7db1.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![4, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .gapLower 4 5, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .gapLower 3 0]

-- Cycle fingerprint d16d4c6bdee11060759e10c5615348308ef11220a0c7233cb2c90bf86d2b310f.
def localCycle00077 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 6, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 2, .triangle 6 1, .triangle 8 0, .triangle 30 1, .triangle 17 0, .corridorLower 1 2]

-- Cycle fingerprint d50f0689ca3f5b708fa8584f1871deda920fdaacad5097eec67299f33b1548df.
def localCycle00078 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 10 1, .triangle 11 0, .triangle 27 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint d51500707382cd7f42fe67a31e72e8f9dbfaf95ab08b2620118c37e877e270e0.
def localCycle00079 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 2, .triangle 11 0, .triangle 33 1, .triangle 26 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint d72a5d1726d3fefcaeeadedeb23533959ec8c2efbb8805c4ccfff47df45dcb17.
def localCycle00080 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 6, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -1, 0, -1, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 2, .triangle 6 1, .triangle 8 0, .triangle 30 1, .triangle 17 0, .gapLower 1 0]

-- Cycle fingerprint da8104f05aedbe4ed1f580c12cfb91b59a10631a5564952788f87b6a5034a31c.
def localCycle00081 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint db3d2474b78a7fa9addc5f899b9f05e673deb5b86ed34febbc6f9c50008d63f5.
def localCycle00082 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint dcbccf0f95fde8a444f9abdfccf746d38696192c79bfd33604e347eed075fdfc.
def localCycle00083 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint dd887980aae9cc40ca5f3a3647de128ec62bbc0c788e662d5ec82eaa198c8d28.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 28 1, .triangle 22 0, .triangle 23 0, .corridorLower 4 6]

-- Cycle fingerprint e0f56c14a6dad46de34103bdc4b330a36cc8b168a72d679bb4f325b12cd146c4.
def localCycle00085 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 27 1, .triangle 26 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint e1642e011339745b55703fa6069eb64dcd27ee25b0df61933e12d8d984dac6b0.
def localCycle00086 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 8 0, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint e25edf239eb51fc34e4ae6f0eabd9d097352256229899a02f614270261a96335.
def localCycle00087 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint e3faed41f2752a5db87cf54df43b36f4c385a855f7c745f85d9b62a135617262.
def localCycle00088 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 6, .distance 2 5, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6]
    constant := ![0, -1, -1, 3, -3, -1, 0, -1, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, false, true, false, false] }
  origin := ![.triangle 30 1, .triangle 17 0, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0]

-- Cycle fingerprint e64487fbd8b9bc9075de250f3db120c9faa2a547f15a099b9d994f1e969ccf88.
def localCycle00089 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint e8b0fa05ff904bbf5192198e07c649b7972af6163ce81c80b6a1089eff15a5fe.
def localCycle00090 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint ebf5e00322d67dc704e4e0fa834968b03eaa1e971c91eec10db94a43ddfe05b2.
def localCycle00091 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 27 0, .triangle 33 1, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint eed99b84b7f9bea298e2cb740fb0f25ecc17bef393f2f0bcb4a65c481d483674.
def localCycle00092 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -1, -1, -1, 0, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 6 0, .triangle 5 0, .triangle 26 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint f0a66818f64356cb8a059b442e12c3bb79538d672ce48628ad34aefadcd90708.
def localCycle00093 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 6 1, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint f862b1d210faed7f302b620cf09910a7b3bb5ae245c5d01eeb3b200f3fc9280a.
def localCycle00094 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint fbabc7c3afee4b3b8ebe73d7a21a9ce47c1f1d007a7ac13577b938f214ed06aa.
def localCycle00095 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint fc81817b37ab1ff310868912dd1214e511719270222f2c2699624a91409bc3a0.
def localCycle00096 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint fd9f249f7f6bdac201f804ae5cf72c2f02c5a22e809ba5af8a309cc3ad93aed2.
def localCycle00097 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint fee918bd098c6fad74df0bc37f3b3c2d8f92718bd250e3993f4ae9498a9ae3f9.
def localCycle00098 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 2, .triangle 11 0, .triangle 27 0, .triangle 15 2, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

def library : Library := fun id => if id < 49 then (if id < 24 then (if id < 12 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))))) else (if id < 18 then (if id < 15 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))) else (if id < 21 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))))) else (if id < 36 then (if id < 30 then (if id < 27 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none))) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)))) else (if id < 33 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none))))) else (if id < 42 then (if id < 39 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none)))) else (if id < 45 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))) else (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none))))))) else (if id < 74 then (if id < 61 then (if id < 55 then (if id < 52 then (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)))) else (if id < 58 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none))) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))))) else (if id < 67 then (if id < 64 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)))) else (if id < 70 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none))) else (if id < 72 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)))))) else (if id < 86 then (if id < 80 then (if id < 77 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none))) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)))) else (if id < 83 then (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none))) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none))))) else (if id < 92 then (if id < 89 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none))) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)))) else (if id < 95 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none))) else (if id < 97 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)))))))

def namedLeaf000 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 6, 5, 0, 4], ![1, 2, 0, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 2, 0, 3], ![1, 4, 5, 2, 0, 3]], proof := .tail 83 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20480)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 3, 5, 6, 0, 4], ![1, 2, 0, 5, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 0, 3, 6], ![4, 1, 2, 0, 3, 5]], proof := .low (![37, 61, 4, 50, 75, 88, 6, 65, 5, 63, 2, 62, 80, 9, 39, 55, 40, 68, 39, 0, 73, 77, 30, 41, 77, 26, 1, 45]) }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20481)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 3, 5, 6, 0, 4], ![1, 2, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 0, 6, 3], ![4, 1, 2, 0, 5, 3]], proof := .low (![37, 61, 4, 50, 75, 88, 6, 65, 5, 63, 2, 62, 80, 9, 39, 55, 40, 68, 39, 0, 73, 77, 30, 41, 77, 26, 1, 45]) }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20482)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 3, 5, 6, 0, 4], ![1, 2, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 6, 0, 3], ![4, 1, 2, 5, 0, 3]], proof := .tail 70 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20483)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 3, 6, 5, 0, 4], ![1, 2, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 2, 0, 3], ![4, 1, 5, 2, 0, 3]], proof := .tail 83 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20484)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 3, 6, 5, 0, 4], ![1, 2, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 1, 2, 0, 3]], proof := .tail 64 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20485)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 3, 6, 5, 0, 4], ![1, 2, 0, 6, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 32 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20486)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 6, 0, 4], ![1, 2, 6, 0, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 6, 0, 3], ![1, 4, 2, 5, 3, 0]], proof := .tail 17 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20487)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 6, 5, 0, 4], ![1, 2, 6, 0, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 2, 0, 3], ![1, 4, 5, 2, 3, 0]], proof := .tail 83 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20488)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 3, 5, 6, 0, 4], ![1, 2, 6, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 6, 0, 3], ![4, 1, 2, 5, 3, 0]], proof := .tail 52 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20489)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 3, 6, 5, 0, 4], ![1, 2, 6, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 2, 0, 3], ![4, 1, 5, 2, 3, 0]], proof := .tail 83 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20490)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 3, 6, 5, 0, 4], ![1, 2, 6, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 1, 2, 3, 0]], proof := .tail 64 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20491)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 3, 6, 5, 0, 4], ![1, 2, 6, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 78 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20492)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 3, 5, 0, 4], ![1, 6, 2, 0, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 2, 0, 3], ![1, 4, 5, 3, 2, 0]], proof := .tail 36 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20493)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 6, 3, 5, 0, 4], ![1, 6, 2, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 2, 0, 3], ![4, 1, 5, 3, 2, 0]], proof := .tail 36 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20494)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 6, 3, 5, 0, 4], ![1, 6, 2, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 1, 3, 2, 0]], proof := .tail 36 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20495)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![2, 6, 3, 5, 4, 0], ![1, 6, 3, 5, 0, 4], ![6, 1, 2, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 3, 1, 2, 0]], proof := .tail 56 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20496)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![6, 2, 3, 5, 4, 0], ![6, 1, 3, 5, 0, 4], ![6, 1, 2, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 3, 2, 1, 0]], proof := .tail 87 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20497)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 6, 3, 5, 0, 4], ![1, 6, 2, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 1, 3, 2, 0]], proof := .tail 44 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20498)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![2, 6, 3, 5, 4, 0], ![1, 6, 3, 5, 0, 4], ![6, 1, 2, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 3, 1, 2, 0]], proof := .tail 46 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20499)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![6, 2, 3, 5, 4, 0], ![6, 1, 3, 5, 0, 4], ![6, 1, 2, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 82 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20500)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 0, 4, 6], ![1, 2, 5, 0, 4, 6], ![1, 5, 0, 2, 3, 6], ![1, 4, 2, 3, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 12 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20501)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 0, 4, 6], ![1, 2, 5, 0, 6, 4], ![1, 5, 0, 2, 6, 3], ![1, 4, 2, 3, 0, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 89 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20502)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 0, 6, 4], ![1, 2, 5, 0, 6, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 2, 3, 0, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 22 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20503)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 0, 6, 4], ![1, 2, 5, 0, 6, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 3, 0, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 86 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20504)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 6, 0, 4], ![1, 2, 5, 0, 6, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 3, 0, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 67 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20505)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 6, 0, 4], ![1, 2, 5, 6, 0, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 3, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 79 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20506)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 6, 0, 4], ![1, 2, 5, 6, 0, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 3, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 90 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20507)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 6, 0, 4], ![1, 2, 6, 5, 0, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 6, 3, 0], ![1, 4, 2, 5, 3, 0]], proof := .tail 81 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20508)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 5, 0, 4], ![1, 2, 6, 5, 0, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 6, 2, 3, 0], ![1, 4, 5, 2, 3, 0]], proof := .tail 18 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20509)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 5, 0, 4], ![1, 2, 6, 5, 0, 4], ![1, 6, 5, 0, 2, 3], ![1, 6, 4, 2, 3, 0], ![1, 5, 4, 2, 3, 0]], proof := .tail 66 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20510)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 5, 0, 4], ![1, 2, 6, 5, 0, 4], ![1, 6, 5, 0, 2, 3], ![6, 1, 4, 2, 3, 0], ![5, 1, 4, 2, 3, 0]], proof := .tail 74 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20511)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 5, 0, 4], ![1, 6, 2, 5, 0, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 6, 2, 3, 0], ![1, 4, 5, 3, 2, 0]], proof := .tail 8 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20512)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 5, 0, 4], ![1, 6, 2, 5, 0, 4], ![1, 6, 5, 0, 2, 3], ![1, 6, 4, 2, 3, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 53 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20513)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 3, 5, 0, 4], ![1, 6, 2, 5, 0, 4], ![1, 6, 5, 0, 2, 3], ![6, 1, 4, 2, 3, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 24 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20514)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 5, 0, 4], ![1, 2, 6, 5, 0, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 2, 3, 0], ![5, 4, 1, 2, 3, 0]], proof := .tail 84 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20515)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 3, 5, 0, 4], ![1, 6, 2, 5, 0, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 2, 3, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 24 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20516)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 3, 5, 0, 4], ![6, 1, 2, 5, 0, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 2, 3, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 96 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20517)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 3, 5, 0, 4], ![6, 1, 2, 5, 0, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 2, 3, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 69 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20518)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 3, 0, 4, 6], ![1, 5, 2, 0, 4, 6], ![1, 5, 0, 2, 3, 6], ![1, 4, 3, 2, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 31 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20519)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 3, 0, 4, 6], ![1, 5, 2, 0, 6, 4], ![1, 5, 0, 2, 6, 3], ![1, 4, 3, 2, 0, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 58 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20520)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 3, 0, 6, 4], ![1, 5, 2, 0, 6, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 3, 2, 0, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 93 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20521)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 3, 0, 6, 4], ![1, 5, 2, 0, 6, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 3, 2, 0, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 25 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20522)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 3, 6, 0, 4], ![1, 5, 2, 0, 6, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 3, 2, 0, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 14 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20523)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 3, 6, 0, 4], ![1, 5, 2, 6, 0, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 3, 2, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 16 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20524)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 3, 0, 4], ![1, 5, 6, 2, 0, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 3, 2, 0, 6], ![1, 4, 3, 2, 0, 5]], proof := .tail 54 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20525)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 3, 6, 0, 4], ![1, 5, 2, 6, 0, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 3, 2, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 49 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20526)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 3, 0, 4], ![1, 5, 6, 2, 0, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 3, 2, 6, 0], ![1, 4, 3, 2, 5, 0]], proof := .tail 21 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20527)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 3, 0, 4], ![1, 5, 6, 2, 0, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 3, 6, 2, 0], ![1, 4, 3, 5, 2, 0]], proof := .tail 83 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20528)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 3, 0, 4], ![1, 6, 5, 2, 0, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 6, 3, 2, 0], ![1, 4, 5, 3, 2, 0]], proof := .tail 95 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20529)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 3, 0, 4], ![1, 6, 5, 2, 0, 4], ![1, 6, 5, 0, 2, 3], ![1, 6, 4, 3, 2, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 29 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20530)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 5, 3, 0, 4], ![1, 6, 5, 2, 0, 4], ![1, 6, 5, 0, 2, 3], ![6, 1, 4, 3, 2, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 48 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20531)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 5, 3, 0, 4], ![1, 6, 5, 2, 0, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 3, 2, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 35 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20532)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 5, 3, 0, 4], ![6, 1, 5, 2, 0, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 3, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 23 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20533)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 5, 3, 0, 4], ![6, 1, 5, 2, 0, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 3, 2, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 82 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20534)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 0, 4, 6], ![1, 2, 5, 0, 4, 6], ![5, 1, 0, 2, 3, 6], ![4, 1, 2, 3, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 12 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20535)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 0, 4, 6], ![1, 2, 5, 0, 6, 4], ![5, 1, 0, 2, 6, 3], ![4, 1, 2, 3, 0, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 89 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20536)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 0, 6, 4], ![1, 2, 5, 0, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 2, 3, 0, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 22 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20537)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 0, 6, 4], ![1, 2, 5, 0, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 3, 0, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 57 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20538)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 3, 5, 0, 6, 4], ![1, 2, 5, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 3, 0, 6], ![4, 1, 0, 2, 3, 5]], proof := .tail 86 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20539)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 6, 0, 4], ![1, 2, 5, 0, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 3, 0, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 33 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20540)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 3, 5, 6, 0, 4], ![1, 2, 5, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 3, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 67 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20541)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 6, 0, 4], ![1, 2, 5, 6, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 3, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 60 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20542)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 3, 5, 6, 0, 4], ![1, 2, 5, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 3, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 79 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20543)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 6, 0, 4], ![1, 2, 5, 6, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 3, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 20 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20544)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 6, 0, 4], ![1, 2, 6, 5, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 6, 3, 0], ![1, 4, 2, 5, 3, 0]], proof := .tail 81 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20545)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 6, 5, 0, 4], ![1, 2, 6, 5, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 2, 3, 0], ![1, 4, 5, 2, 3, 0]], proof := .tail 18 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20546)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 3, 5, 0, 4], ![1, 6, 2, 5, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 2, 3, 0], ![1, 4, 5, 3, 2, 0]], proof := .tail 72 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20547)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 3, 5, 6, 0, 4], ![1, 2, 5, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 3, 6, 0], ![4, 1, 2, 3, 5, 0]], proof := .tail 90 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20548)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 3, 5, 6, 0, 4], ![1, 2, 6, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 6, 3, 0], ![4, 1, 2, 5, 3, 0]], proof := .tail 81 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20549)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 3, 6, 5, 0, 4], ![1, 2, 6, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 2, 3, 0], ![4, 1, 5, 2, 3, 0]], proof := .tail 18 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20550)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 6, 3, 5, 0, 4], ![1, 6, 2, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 2, 3, 0], ![4, 1, 5, 3, 2, 0]], proof := .tail 72 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20551)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 3, 6, 5, 0, 4], ![1, 2, 6, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 3, 0], ![4, 5, 1, 2, 3, 0]], proof := .tail 97 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20552)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 6, 3, 5, 0, 4], ![1, 6, 2, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 3, 0], ![4, 5, 1, 3, 2, 0]], proof := .tail 72 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20553)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 6, 3, 5, 4, 0], ![1, 6, 3, 5, 0, 4], ![6, 1, 2, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 3, 0], ![4, 5, 3, 1, 2, 0]], proof := .tail 94 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20554)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 2, 3, 5, 4, 0], ![6, 1, 3, 5, 0, 4], ![6, 1, 2, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 3, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 42 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20555)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 3, 6, 5, 0, 4], ![1, 2, 6, 5, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 3, 0], ![5, 4, 1, 2, 3, 0]], proof := .tail 74 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20556)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 6, 3, 5, 0, 4], ![1, 6, 2, 5, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 3, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 24 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20557)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 6, 3, 5, 4, 0], ![1, 6, 3, 5, 0, 4], ![6, 1, 2, 5, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 3, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 96 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20558)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 2, 3, 5, 4, 0], ![6, 1, 3, 5, 0, 4], ![6, 1, 2, 5, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 3, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 69 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20559)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 3, 0, 4, 6], ![1, 5, 2, 0, 4, 6], ![5, 1, 0, 2, 3, 6], ![4, 1, 3, 2, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 59 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20560)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 3, 0, 4, 6], ![1, 5, 2, 0, 6, 4], ![5, 1, 0, 2, 6, 3], ![4, 1, 3, 2, 0, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 58 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20561)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 3, 0, 6, 4], ![1, 5, 2, 0, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 3, 2, 0, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 93 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20562)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 3, 0, 6, 4], ![1, 5, 2, 0, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 3, 2, 0, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 34 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20563)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 5, 3, 0, 6, 4], ![1, 5, 2, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 3, 2, 0, 6], ![4, 1, 0, 2, 3, 5]], proof := .tail 92 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20564)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 3, 6, 0, 4], ![1, 5, 2, 0, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 3, 2, 0, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 33 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20565)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 5, 3, 6, 0, 4], ![1, 5, 2, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 3, 2, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 85 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20566)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 3, 6, 0, 4], ![1, 5, 2, 6, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 3, 2, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 16 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20567)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 6, 3, 0, 4], ![1, 5, 6, 2, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 3, 2, 0, 6], ![1, 4, 3, 2, 0, 5]], proof := .tail 27 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20568)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 5, 3, 6, 0, 4], ![1, 5, 2, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 3, 2, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 16 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20569)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 5, 6, 3, 0, 4], ![1, 5, 6, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 3, 2, 0, 6], ![4, 1, 3, 2, 0, 5]], proof := .tail 91 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20570)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 3, 6, 0, 4], ![1, 5, 2, 6, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 3, 2, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 49 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20571)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 6, 3, 0, 4], ![1, 5, 6, 2, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 3, 2, 6, 0], ![1, 4, 3, 2, 5, 0]], proof := .tail 27 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20572)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 5, 3, 0, 4], ![1, 5, 6, 2, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 3, 6, 2, 0], ![1, 4, 3, 5, 2, 0]], proof := .tail 83 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20573)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 5, 3, 0, 4], ![1, 6, 5, 2, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 3, 2, 0], ![1, 4, 5, 3, 2, 0]], proof := .tail 95 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20574)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 5, 3, 6, 0, 4], ![1, 5, 2, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 3, 2, 6, 0], ![4, 1, 2, 3, 5, 0]], proof := .tail 49 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20575)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 5, 6, 3, 0, 4], ![1, 5, 6, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 3, 2, 6, 0], ![4, 1, 3, 2, 5, 0]], proof := .tail 21 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20576)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 6, 5, 3, 0, 4], ![1, 5, 6, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 3, 6, 2, 0], ![4, 1, 3, 5, 2, 0]], proof := .tail 83 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20577)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 6, 5, 3, 0, 4], ![1, 6, 5, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 3, 2, 0], ![4, 1, 5, 3, 2, 0]], proof := .tail 95 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20578)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 6, 5, 3, 0, 4], ![1, 6, 5, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 3, 2, 0], ![4, 5, 1, 3, 2, 0]], proof := .tail 95 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20579)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 6, 3, 5, 4, 0], ![1, 6, 5, 3, 0, 4], ![6, 1, 5, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 3, 2, 0], ![4, 5, 3, 1, 2, 0]], proof := .tail 11 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20580)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 2, 3, 5, 4, 0], ![6, 1, 5, 3, 0, 4], ![6, 1, 5, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 3, 2, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 87 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20581)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 6, 5, 3, 0, 4], ![1, 6, 5, 2, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 3, 2, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 48 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20582)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 6, 3, 5, 4, 0], ![1, 6, 5, 3, 0, 4], ![6, 1, 5, 2, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 3, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 23 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20583)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 2, 3, 5, 4, 0], ![6, 1, 5, 3, 0, 4], ![6, 1, 5, 2, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 3, 2, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 82 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20584)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 3, 0, 4, 6], ![5, 1, 2, 0, 4, 6], ![5, 1, 0, 2, 3, 6], ![4, 3, 1, 2, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 3 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20585)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 3, 0, 4, 6], ![5, 1, 2, 0, 6, 4], ![5, 1, 0, 2, 6, 3], ![4, 3, 1, 2, 0, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 15 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20586)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 3, 0, 6, 4], ![5, 1, 2, 0, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 3, 1, 2, 0, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 7 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20587)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 3, 0, 6, 4], ![5, 1, 2, 0, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 1, 2, 0, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 47 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20588)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![2, 5, 3, 6, 4, 0], ![1, 5, 3, 0, 6, 4], ![5, 1, 2, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 1, 2, 0, 6], ![4, 1, 0, 2, 3, 5]], proof := .tail 38 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20589)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 3, 6, 0, 4], ![5, 1, 2, 0, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 1, 2, 0, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 28 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20590)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![2, 5, 3, 6, 4, 0], ![1, 5, 3, 6, 0, 4], ![5, 1, 2, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 1, 2, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 28 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20591)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 3, 6, 0, 4], ![5, 1, 2, 6, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 1, 2, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 10 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20592)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 6, 3, 0, 4], ![5, 1, 6, 2, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 1, 2, 0, 6], ![1, 4, 3, 2, 0, 5]], proof := .tail 71 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20593)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![2, 5, 3, 6, 4, 0], ![1, 5, 3, 6, 0, 4], ![5, 1, 2, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 1, 2, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 98 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20594)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![2, 5, 3, 6, 4, 0], ![1, 5, 6, 3, 0, 4], ![5, 1, 6, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 1, 2, 0, 6], ![4, 1, 3, 2, 0, 5]], proof := .tail 71 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20595)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![2, 5, 6, 3, 4, 0], ![1, 5, 6, 3, 0, 4], ![5, 6, 1, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 1, 2, 0, 6], ![4, 3, 1, 2, 0, 5]], proof := .tail 13 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20596)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 3, 6, 0, 4], ![5, 1, 2, 6, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 1, 2, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 51 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20597)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 6, 3, 0, 4], ![5, 1, 6, 2, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 1, 2, 6, 0], ![1, 4, 3, 2, 5, 0]], proof := .tail 71 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20598)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 5, 3, 4, 6, 0], ![1, 6, 5, 3, 0, 4], ![5, 1, 6, 2, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 1, 6, 2, 0], ![1, 4, 3, 5, 2, 0]], proof := .tail 83 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20599)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 5, 3, 6, 4, 0], ![1, 5, 3, 6, 0, 4], ![5, 1, 2, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 1, 2, 6, 0], ![4, 1, 2, 3, 5, 0]], proof := .tail 51 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20600)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 5, 3, 6, 4, 0], ![1, 5, 6, 3, 0, 4], ![5, 1, 6, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 1, 2, 6, 0], ![4, 1, 3, 2, 5, 0]], proof := .tail 71 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20601)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 5, 3, 6, 4, 0], ![1, 6, 5, 3, 0, 4], ![5, 1, 6, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 1, 6, 2, 0], ![4, 1, 3, 5, 2, 0]], proof := .tail 83 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20602)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 5, 6, 3, 4, 0], ![1, 5, 6, 3, 0, 4], ![5, 6, 1, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 1, 2, 6, 0], ![4, 3, 1, 2, 5, 0]], proof := .tail 19 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20603)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 5, 6, 3, 4, 0], ![1, 6, 5, 3, 0, 4], ![5, 6, 1, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 1, 6, 2, 0], ![4, 3, 1, 5, 2, 0]], proof := .tail 83 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20604)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 6, 5, 3, 4, 0], ![1, 6, 5, 3, 0, 4], ![5, 6, 1, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 6, 1, 2, 0], ![4, 3, 5, 1, 2, 0]], proof := .tail 64 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20605)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 6, 5, 3, 4, 0], ![1, 6, 5, 3, 0, 4], ![6, 5, 1, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 3, 1, 2, 0], ![4, 5, 3, 1, 2, 0]], proof := .tail 43 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20606)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 2, 5, 3, 4, 0], ![6, 1, 5, 3, 0, 4], ![5, 6, 1, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 6, 1, 2, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 76 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20607)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (20480 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 20480 ≤ id.val) (hhigh : id.val < 20608) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 20480)) = true := by
  let j : Fin 128 := ⟨id.val - 20480, by omega⟩
  have hsum : 20480 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (20480 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard160
