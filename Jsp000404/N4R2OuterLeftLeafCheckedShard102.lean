import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard102
open N4R2OuterLeftReplay

-- Cycle fingerprint 01cea0dc875d7d7dd92635fcd2d925b33d2b61ed34c5115a0899a940b6fed7d3.
def localCycle00000 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 02aebb10659efd8c2b8e727dd91be7af4b4fec1ed181d68b6ae7136a0a7b4665.
def localCycle00001 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 9 0, .gapLower 0 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 02cb8fe6948b9495c90f9956277e71b83a87c010a44258b82eecdd6ce638cc54.
def localCycle00002 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5]
    constant := ![-1, 0, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 2 2, .triangle 12 0]

-- Cycle fingerprint 0309c43e380cca72abe30b6836c402e4a06b9e633c12e91d500c4b842bd8f436.
def localCycle00003 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 34 2, .triangle 13 0, .triangle 2 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 075c90951f104b062c5c74d0d0e9d598d6eecb69f425c86a972d188a8b4831e3.
def localCycle00004 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 077270af95a4d53c50dbbe8fafb8dbcc9c77067089c3a4e636605fce7aae4e99.
def localCycle00005 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 0a0e4651d821b4e64771c5aa3780c83e67461faa535ffe324b853edafe7f544f.
def localCycle00006 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 10 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 0c02687a44f6ed65897f7b96b9cacfa4d0baae80d641dbeb220deda82663336d.
def localCycle00007 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 31 1, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 0c98bf21e16ab2bd195a14a0c3d6e390f5e105f3663608f79c2e83115c5c04bf.
def localCycle00008 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![-2, -1, -1, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint 0ce8aaa403c99bef6f980fbb55bdb5af3de2c69c84ec3051d2fd282c5ada7731.
def localCycle00009 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 0d52f419d69e838b60e81628696380c851d869700e4477da22bf0dd7433d51f7.
def localCycle00010 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 0db6c0fdcfcc36aa2b0d745f259ceaa4b6708f80061728e40ef6247f246e1208.
def localCycle00011 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 20 0, .triangle 31 1, .triangle 9 0, .gapLower 0 2, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 0ec6f092a739f864af4b74100a4195cf3113cd0cea70fd967b81287e9ad018cf.
def localCycle00012 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 32 0, .triangle 13 0, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 1052ecfc05e2d08a88de00cb2f87d3fd91988bf8522418eae35dffb0580497d7.
def localCycle00013 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -2, -1, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 4 0, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint 137f4ca6b6f1a8e951812d7886d861dee84f89be8ccd67e654860d0904aac5df.
def localCycle00014 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 187fc548a10358d804862a87521094cdec8070159fd58d21bc55d8ed74b902b1.
def localCycle00015 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 1ba0a3fea97263d2936abccbae59254796a989a9cd56b3743afe3eaf03cd4cd6.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 24 1, .gapLower 1 2, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 1c4b431bf1a2a5cdd477c64f061c13f520d8dd4403b67b06a4cb3215e26fe944.
def localCycle00017 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5, .distance 1 6]
    constant := ![-1, -1, -1, 4, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint 1cf0f10abecb55b66087c6b8c5075749534064326f27e14b367bab8a27c886fe.
def localCycle00018 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint 1d503706b62587102934d26c8d7a74d7131453e8eda2cc66d73545d49f9fe9fc.
def localCycle00019 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4]
    constant := ![-3, 0, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 2, .triangle 0 2, .gapUpper 2 2, .gapLower 4 3]

-- Cycle fingerprint 1e0c237785b27fbd2b12bfb30d19a1591f838c698dd9d9fb04af7f2383a7cc38.
def localCycle00020 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 22 0, .triangle 31 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 1f783dad880d375bba98c8fe145c26f45e335007df6e4a536bc68ca17532b813.
def localCycle00021 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 223cfe2a35dcfe1f74b2ddaeaa7b29fca99c71c3ba0fc096d7115058f6285f84.
def localCycle00022 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 3 4]
    constant := ![0, 0, -1, 0, -3, -1, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 32 2, .triangle 33 1, .triangle 10 0, .gapLower 0 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 19 0]

-- Cycle fingerprint 22cbffb45f99b3d1d49d007ba2c1857b17ad65608779bfa73bcf4926c908f9d2.
def localCycle00023 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0, .triangle 19 1, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 24270c63e3ad3d46e581a9913c0cdeecf6b56c8d7f26d6b38027669dfa1ead91.
def localCycle00024 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 2 0, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 2532b5935db707024e1780be6e3bbd43e2f73cad0c6b25654b74617107a4fc95.
def localCycle00025 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .triangle 12 0, .triangle 2 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 28b91a692fbe58017b818e51336f8947efbfbf1f2b41c2a732533c8e43ae8dfe.
def localCycle00026 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 13 0, .triangle 2 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 28bf3a0b67d029d28fc107e57046ff33e6d0a97823f2d518822acbb43bd95269.
def localCycle00027 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, -1, -2, -1, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0]

-- Cycle fingerprint 2a278426303e726f112d90866748ad491a2244445173c88b474e9835cbf7a8a2.
def localCycle00028 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 2ccfdab729563dc7e2e5fdb80ede1d4ecdc6741bb40a563594b250b613dafbc7.
def localCycle00029 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 2dfba42b769d72dc733196571ebab7bc4614d0d09d709fd87ff225a84f464d76.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 0, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 2e32a0f6c27015183eaf82c3b9e99140c2cfc0b63e8b5c68331d1c5ad687fdde.
def localCycle00031 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0]

-- Cycle fingerprint 2fca32c6641cb5a6164f362efb68e645a0148afab390baca93450eb165b8cc9b.
def localCycle00032 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 9 0, .gapLower 0 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 303d4a82c0c7ffa7c734bd58be0ce22a8acbaabcb561742e4eac69194aef0228.
def localCycle00033 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3]
    constant := ![-2, 0, -2, -1, -1, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 24 2, .gapLower 1 3, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint 310940e32d672056fbaf7879aac76f36f04c16016c639decf850b9904ea1334f.
def localCycle00034 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 22 1, .gapLower 1 2, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 3326e809d105197b10d2daac9c101c5c781baaf6c6d12619995b59fd73bf7f62.
def localCycle00035 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 3338f177e4e90ca5eb2d0647ba7849d6aeb792c36aa5ccc402471b99de0d5f7e.
def localCycle00036 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -1, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 4, .triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 33afa973b286000b78a81732291956859e553ff6bc12db54c0043516ba308324.
def localCycle00037 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 346a561492bd032beb75edfcf90e6d33fd5fb68b674cb53a58913950ed1c3331.
def localCycle00038 : Cycle where
  length := 13
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 10 0, .triangle 1 1, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 383c54e6a25ed265e11589505aa4ebe35d83e73744cffbad923fb874eed61df6.
def localCycle00039 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 31 1, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 38cc5e1e0ec12548d4d54f9f7d6bd7679e8692c1263e2a379f7452014488b902.
def localCycle00040 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, true, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 33 0, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 3b1c4be8644e9520705c01e4060851ae57260f62b1f65b90177ce8a2c64ae6f9.
def localCycle00041 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint 3b503e6e0f25426ff59bd24657ede601c0f2389fd139ca7d713562b83914ba32.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 3 4, .distance 3 6, .distance 3 5]
    constant := ![-1, 0, -1, -1, 1, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.triangle 10 0, .gapLower 0 2, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .triangle 19 0, .triangle 32 2, .triangle 33 1]

-- Cycle fingerprint 3b86d3bc64402afd05df642051b5097505f2b8f8e1db2a63804de5f3211ce2f0.
def localCycle00043 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 3cc6c0643c11c1e0bce2490adfaab66ebe1c678c68e7b94425284ae3ab251cc8.
def localCycle00044 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 22 0, .triangle 19 1, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 3d0ded165f33f6cc1d55a0ee2e2f407ef8350568fb454947450a7d9f6b2a3f04.
def localCycle00045 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 423db4d9a4656d808717fec2f971b583785604e4e744c09db23a555f2d7101e1.
def localCycle00046 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-3, -1, 4, -1, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 20 0, .triangle 31 1, .triangle 9 0, .gapLower 0 2]

-- Cycle fingerprint 4242ae111ebcfae266b45dc965b281dd8b0c3b5525d368fc4cb4b8acbb68019d.
def localCycle00047 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 4336b228635f202e103ccd1589419773bad2b6907e36a7236f7ca9865c0fad1f.
def localCycle00048 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 20 0, .triangle 31 1, .triangle 9 0, .gapLower 0 2, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint 48243b5d9f8df77e6ed81ad3bfff7d8d5fb5b6cef4ee84f3b4df12a03e9e889b.
def localCycle00049 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 0, .triangle 31 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 4977ab606879d197aee7053e99a86b1a7a7e5f1b0ad9b3c12f7d0c69795a5527.
def localCycle00050 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 31 1, .triangle 12 0, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 4a065aed7a121b06a469b29bcc98ddd06ef80616a1822c97471517e366db563f.
def localCycle00051 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -1, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .triangle 4 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 4e6fb2ba9260d24de1aad22fea2b4bdf7c43f917106f40bf92d6993b2e0d79c2.
def localCycle00052 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .gapLower 4 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 4eaa466ca4b4189e7e68a6a1346677d4727f85ba0fe85a507e67b5d55ba31ded.
def localCycle00053 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 31 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 4ed91d0263873d79a160e3330ce64464c2ad1ed2dd0736536ed0e7e4bcb34c07.
def localCycle00054 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 4f1516040465510986ba9f08b491edefd26a71c9353b37b79ea67c4666f78dff.
def localCycle00055 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 34 1, .triangle 12 0, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 50316ea408a0479278ac30009110c272ad9d7be94e63d47d6869c99e6495fac2.
def localCycle00056 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 6, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint 50603a69905c1f19356fff811094eafae584ae55792af04f5931a30342ee19b1.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 50b2ba7908da3c34a4175a4ec0656ca29b1d87ef070fdfc8c21d3f41d75652cf.
def localCycle00058 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5]
    constant := ![-3, 0, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 2, .triangle 0 2, .gapUpper 2 2, .gapLower 5 4]

-- Cycle fingerprint 5121f1b3eb03e30983accaf6581e4d9a6967488e8ae7452cf87fbc29055bbe13.
def localCycle00059 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![0, 2, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true] }
  origin := ![.triangle 0 2, .gapUpper 2 2, .triangle 30 1, .triangle 34 0, .triangle 31 0, .triangle 9 0, .triangle 1 1]

-- Cycle fingerprint 516a6e6656257f1b84f3cdad4264a59f0b86a73cf93bd3017c3b79dce2bf6ec6.
def localCycle00060 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 52890d41ef47f90b0b8b1fadc377e67dca76feddbf8370f23dea94adcf89f8ce.
def localCycle00061 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 6]
    constant := ![-1, -1, -1, 2, -2]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 58beef1a75d8dd1b02b3d10071532ce283f5c61d4bf2f74f902f1df781c63bfc.
def localCycle00062 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![-3, -1, 0, 2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 3, .triangle 3 0, .gapLower 0 1, .gapUpper 2 2, .gapUpper 5 5, .gapLower 6 5, .triangle 23 0]

-- Cycle fingerprint 58c5ba24f045893b5a6cbbc25c2531bc7d0c390fa66a19c2f8b0d98775ec4d63.
def localCycle00063 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![-1, -1, -1, 2, -2]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 633bc1b7b920b86e8f5c7d00e7d2587f45fdca8f7abbb9d0af48d7972620395b.
def localCycle00064 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 633d44267e9acca4a9443409b20ac4f20219d5ed6449d5ffd103101fb0513ee2.
def localCycle00065 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 6650e12a8a3dfc54b51d84123bce7740cc223482fa5b81debf72d779969165a9.
def localCycle00066 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 21 2, .triangle 23 1, .triangle 22 2, .gapLower 1 2, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint 67ff0d171e49c0cb1c395887fd3ee03dd62ef3ca291c02b9066f21fbafc84764.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 698277a0b14a35d2a951a08e5c325a2d3f0935310e727e4d718d21ffe41337e9.
def localCycle00068 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![-1, -1, -1, 2, -2]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 6a8b3885782a7c22a75b478281ceae9f99c35722b871978dae3572057295fea8.
def localCycle00069 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 3 0, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint 6ab67107e6971ec80d1b142831bc157107203953c4553382d5f873abf61be5e4.
def localCycle00070 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 0, .gapLower 3 2, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 6cc7e8ccc804b62d857aec71c4bb4e3f4d67557294305f6920de19a160e344c4.
def localCycle00071 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 6dec8d463e85f686596e078d122ef52f31838a9f826eb573862322a486f8fdfd.
def localCycle00072 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -3, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint 6e46c3a02c13d66a4a20474d40ce38b10e2813a3e1a71bfe936543551df8a13a.
def localCycle00073 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 6e5561a2bf02519384d37d5e9abc8ce7dfe6e24eb37fed7cc2ab4cb38704bc1a.
def localCycle00074 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 6e5f2e1660748d00faf79e37aef60ea92d473b33de9b2bbdb8f813952ab4a463.
def localCycle00075 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4]
    constant := ![-2, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0]

-- Cycle fingerprint 6efab136090ab2e0fb6f89835625889315a7120d813220d163a1baaa164416cd.
def localCycle00076 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 71512eb0c44cc43f8f5f55d7c19ba9d1af78cf4467758333a50b55e7645d61d5.
def localCycle00077 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, -1, -2, -1, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 3 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0]

-- Cycle fingerprint 727af6a62f70b57bac8e3a82817057b2084d9e1f58624848c41f19ca57635966.
def localCycle00078 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 2 0]

-- Cycle fingerprint 76140d273d683f9bfdc6418fdb2f5da47a51bef8aa2e391447526b7572958a19.
def localCycle00079 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 33 2, .triangle 21 0, .triangle 19 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 7655324447b498ed49a7d77d9936444af546c7edb4d5c1df2b35250e57e7c377.
def localCycle00080 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 12 0, .triangle 2 1, .triangle 4 0, .triangle 21 1, .corridorLower 3 6]

-- Cycle fingerprint 77da7790cce097379f4d6621ca57f6b4da32d93f564512ae5ac85da59a8c9344.
def localCycle00081 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-3, -1, 4, -1, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 21 0, .triangle 32 1, .triangle 9 0, .gapLower 0 2]

-- Cycle fingerprint 78be09628c0d9194528f8430074a3e77162307961777c089501a044b2bacd350.
def localCycle00082 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -2, -1, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 3 0, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint 793c459b544ab473d28ab5620d8270e5fc72607ac534ef83e346a0071e590520.
def localCycle00083 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 7b2221fe8a2253939b294231297d49a85779cc1ba4dd7f07e44bf6f2114e5513.
def localCycle00084 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 7cc0e3ff3eea711be849566f015fbca9cff2acbc97f788f50cae5c1c1e3961cb.
def localCycle00085 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -3, -1, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 4, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 7d9897a6ae839ae0b05df94a6b63943c1710e5892c9d1a507eb1a78bc6ec9766.
def localCycle00086 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 9 0, .gapLower 0 2, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3]

-- Cycle fingerprint 809bee40669fb65ef2da99ff9e9755533d039a0073e78bfd42d9add2360c8d18.
def localCycle00087 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 2 6, .theta 6, .theta 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5]
    constant := ![-1, 0, 0, 2, -2, 0, 3, 0, -1, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, true, false, false] }
  origin := ![.triangle 12 0, .gapLower 0 3, .triangle 5 1, .gapUpper 2 2, .gapUpper 6 6, .thetaNext 5, .corridorUpper 2 5, .triangle 17 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 31 0]

-- Cycle fingerprint 8346300ecb1d65f3ac98aed749e237cf1e38b04570e231ce459bf430aa34cd0c.
def localCycle00088 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 1 4, .triangle 22 2]

-- Cycle fingerprint 837ac5cf4a53538fa6b6dad39e85527b61d3d86dda133e0f391608ef36a4d8e8.
def localCycle00089 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .triangle 22 1, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 84b75135b28c35844954271a97847c5ef7b620c80e93330ce3cde16829f6f310.
def localCycle00090 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -3, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint 869362f9cc48ab60e44ee9c060305f8243e5c21248a98fd6f042f6bfdfcc4b56.
def localCycle00091 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 12 0, .triangle 6 1, .triangle 8 0, .triangle 18 2, .triangle 21 1, .corridorLower 3 6]

-- Cycle fingerprint 881b409489d6575fdfa72335b4398aeacda3fede23b2a1aa9f802c8e92eee129.
def localCycle00092 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![-2, -1, -1, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .triangle 20 2]

-- Cycle fingerprint 8af30e6ca6b93e027622403516473ffe5d19a7723bc9a2febedce4ea653dc6c1.
def localCycle00093 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, 0, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true, true, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 8de3f290ca9e76ce262c4f1256178e113517fc591211187cbb084a7a354de443.
def localCycle00094 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![-2, -2, -1, -1, -1, 4, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .triangle 20 2]

-- Cycle fingerprint 90ed888ccd250b539b66a663bdedb717d535fb7505cbb62ebb9984e01afe255a.
def localCycle00095 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 915fbeea49634d655fb1ab6e2cd551bd75ca335142d2548029437e75bc6df3fb.
def localCycle00096 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 21 2, .triangle 23 1, .gapLower 1 3, .triangle 3 0, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint 91b73fc902a8413d6e9ab848fc93943a9f42a7d8f5e8fb2c2f355da029673aeb.
def localCycle00097 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -2, -1, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 2 0, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint 92e1e27b22fe22fd7892f16b118311f49e9aae5f2c87185e62950c751ad6b9f4.
def localCycle00098 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 9654b96f690737555aa1291628bb91b73d82b15bac5cd0625b29a12e68bcc3a5.
def localCycle00099 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 3 4, .distance 3 6, .distance 3 5]
    constant := ![-1, 0, -2, -1, 2, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.triangle 10 0, .gapLower 0 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 19 0, .triangle 32 2, .triangle 33 1]

-- Cycle fingerprint 968d30c47e922eb9b1f52913fee6714b676e2364277422ce88c3bae4383b6fc6.
def localCycle00100 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 21 0, .triangle 32 1, .triangle 9 0, .gapLower 0 2, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint 971085d8f34c95aa0e0e720ff49cca964e8e8e0c9f8afa82d86940ac3e197a64.
def localCycle00101 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .triangle 19 1, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 9a94e6b930165762a6211077cc2964c51e06955d1eef97da5a5dae7468678336.
def localCycle00102 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 9b0a682d5f8c894fdf587b1cfe3308fd80a43bc7784c7b2e8350dd39f560af1a.
def localCycle00103 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 22 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0]

-- Cycle fingerprint 9b25d25542a977598c75e31c112b0787604d42c468121842a1e4de8f659bfc02.
def localCycle00104 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 21 0, .triangle 32 1, .triangle 9 0, .gapLower 0 2, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 9d14d1dc17e161bd93c124898d818697ec9fd18f8afebafee59fb6fa07834f53.
def localCycle00105 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .gapLower 4 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 9f590a902500b504d686e14d183ceeaf74e198bff9e7dcffe0004d2aca68b80f.
def localCycle00106 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![0, -2, -1, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 22 1, .gapLower 1 2, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .triangle 20 2]

-- Cycle fingerprint a294133b13bc40d4e4a39522cae87679996ab74b82fd1e1b75fa2879fbd97eb7.
def localCycle00107 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![0, 2, 0, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, false, false, false, true] }
  origin := ![.triangle 0 2, .gapUpper 2 2, .triangle 18 2, .triangle 24 1, .triangle 34 0, .triangle 31 0, .triangle 9 0, .triangle 1 1]

-- Cycle fingerprint a301fa5b19d44dc5375d0979ecc3e9f91774602b18ec20df8baf80f66ab248aa.
def localCycle00108 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, -1, -1, -2, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 3 0, .triangle 0 0, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint a321d883c6f1e448c2a4ca3d8137da6df654cfba06809c4e37724dc57241bd55.
def localCycle00109 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 5]
    constant := ![2, 0, -1, 0, -2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, false, false, true] }
  origin := ![.gapUpper 5 5, .triangle 34 2, .triangle 29 0, .triangle 16 2, .gapLower 1 3, .triangle 3 0, .gapLower 0 1, .gapUpper 2 2]

-- Cycle fingerprint a9a35ea68b198be849f83931d281c0186472d649528265663906749a48925f2c.
def localCycle00110 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -1, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .triangle 4 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint ab43e25cd1edc8e6f93e3d3a0e9d46cad4a8064265a61caaedfe90c364832317.
def localCycle00111 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -2, -1, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 3, .triangle 3 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint abbf10555ff855bf5d590bbbed06f13cbab8a7f69b8a7d9aae233464449f19b9.
def localCycle00112 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 34 0, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint afb6149b137d1689f665fd7dc9c331e61d0c380174d89f27c76ce42929b8de3d.
def localCycle00113 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -1, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 4, .triangle 2 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint afb9e431352ba479c4349359346b5351ed1eb087646b2390e398a198b26ac80e.
def localCycle00114 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -3, -1, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .triangle 4 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint b161542881b04bba5172c6f2617cb080ba2e78766c471998ac121aa2ceb2585f.
def localCycle00115 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![2, 0, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true] }
  origin := ![.gapUpper 2 2, .triangle 30 1, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 12 0, .triangle 6 1]

-- Cycle fingerprint b41084b83046950b98754ebf730bfe5dda08ff51a48df31f24fe4ade8a958ef6.
def localCycle00116 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint b4cbe103184cf146c6037dc54fbb5839207f85f150bae554bd95f6dec95d379a.
def localCycle00117 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 3 0]

-- Cycle fingerprint b522466e37264e3f6bd593c4acdbf334a2df1f9f2627c321e8afdbb4f10e3532.
def localCycle00118 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .gapLower 3 2, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint b570f1b8fd5a1ed8e9f109da801ab49664e12e3dc4539732002dfb16a31225fd.
def localCycle00119 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .triangle 2 0, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint b69d361c9f08472c85eb6603d06fe89c1ad8690413fb04a983229d7ec0e5f835.
def localCycle00120 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint b7f8760b11852dbcb2fb948b39cb34664fa85b377f1c251bfeed656f3f89f122.
def localCycle00121 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 12 0, .triangle 13 0, .corridorLower 4 6, .thetaNext 3]

-- Cycle fingerprint b980e8843d6c7febe9c043313c350f274c10a907fc22b9655082410bd936944d.
def localCycle00122 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 3 4, .distance 3 6, .distance 3 5]
    constant := ![-1, 0, -1, -2, 2, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.triangle 10 0, .gapLower 0 2, .triangle 0 0, .gapLower 1 0, .gapLower 1 6, .triangle 19 0, .triangle 32 2, .triangle 33 1]

-- Cycle fingerprint bbae65b536c9780f92f69c59225476acdec13d916ac90ccab9a6fb8ac324a13e.
def localCycle00123 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint bc70538997b39341d8f354e8b47bbe57cba77866d44a5147bceff487eb302d15.
def localCycle00124 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint bcedfed5dc72315041535a2bd7b279d13ecdea59a6fe1482357b94c6272cca61.
def localCycle00125 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -1, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .triangle 4 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint be2dc62434dc905ce3e55dd6415f4eb69e838a59529bd1c73a4c9dbf4d8c23ec.
def localCycle00126 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4]
    constant := ![0, 0, -1, 0, -2, -2, 0, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 32 2, .triangle 33 1, .triangle 10 0, .gapLower 0 2, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 0]

-- Cycle fingerprint c067170ea2aa96c01194edeed28f096cb0999fbe98c1d72ae8af531a396e2f09.
def localCycle00127 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6]
    constant := ![0, -2, -1, -1, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 23 2]

-- Cycle fingerprint c180f61cd083c16182e4632c0d3af72530d9ff715a4ce39e0a015636b01271ff.
def localCycle00128 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, -1, -1, -2, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .triangle 2 0, .triangle 0 0, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint c3c44b86ec30a1f70207fb4b3ebb1648230169da54169745ca1ec93c4761a636.
def localCycle00129 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 4, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 1 5, .triangle 19 1]

-- Cycle fingerprint c4f373e389549d1bce243d6cc266d87a5484e7dc11a6e28d64fb2b7a95c4fcdb.
def localCycle00130 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .triangle 13 0, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint c6c4da7dbb19e254736e537b1ff23b87d2dcdd26426c8f9913d06cdd076c1d9d.
def localCycle00131 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint c82510ffc011f8d88954ed776c8fe424a175669394273af161a38ad92ff19b8f.
def localCycle00132 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, -1, 0, -1, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 20 0, .triangle 31 1, .triangle 9 0, .gapLower 0 2, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint c93903ff99c2bc7ebad62415860854ae62f6843f87d40cbe06ca6d6509fb1122.
def localCycle00133 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 12 0, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint cada10021bd681f65c192e21f96262bb9ead563b0499a433f2404a5531ff543c.
def localCycle00134 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3]
    constant := ![-2, 0, -2, -1, -1, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 3 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint cb2d49aeea77f753df70514ce214270571d86928a8328b21ef25c32fc37a6ccc.
def localCycle00135 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 1 6]
    constant := ![-1, -1, -1, 4, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint cd4439b57fdcb2fc73fe26f149c3dc4be4c21689e5bbcb307425f630a6be1a4c.
def localCycle00136 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 19 0, .triangle 9 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint cdf80b0d52091f281f3b065206be8df43ac9bc14e9891163639327c336e2cdf8.
def localCycle00137 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint cdff4bd3ba9adf74f175fb0540b5b9d2651d3af16f1f614af8572269afec6580.
def localCycle00138 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 3, .distance 3 4, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-1, 0, 0, -1, 0, -1, -3, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 0, .triangle 32 2, .triangle 33 1, .triangle 10 0, .gapLower 0 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint cfecf1b93a1840470b365c0ad0224574cbb0ced33d7d3b7110ccb67b2fb90f0e.
def localCycle00139 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint d120db563c8ccebde67ccf0f9b340cef81e0f3b25124db9bcd79fb89fe4e0f11.
def localCycle00140 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 5, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 1 5, .triangle 20 1]

-- Cycle fingerprint d4cb1d6a60a8cff20d2e6059991bd2fd4137b1b34778560eba8b3935fa4b1031.
def localCycle00141 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint d4ef3c225725edbcaab0f66eab0722c0195b346c8f10d88eba157b4775e28bce.
def localCycle00142 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint d502fd90f6ad279f358a7fb14d9f493fa013a0d14adeeb73f6c69098f11ca158.
def localCycle00143 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint d5f366ae48c1cfad7e6d7d69f482bda8746b640b4ef5543b52e870d56a444837.
def localCycle00144 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 2, .triangle 12 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint d820396b9f1446a1be88eda976cf0a8c12040588ddd3097295c5b8b24e15c1f4.
def localCycle00145 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint d8c13620fefe90572141a635c4c937b31faf4a62d004ddbc1b67f86c0401a797.
def localCycle00146 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 6]
    constant := ![-2, -2, -1, -1, -1, 4, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .triangle 3 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .triangle 21 2]

-- Cycle fingerprint d986790ba0dd845f23e7fa99eeb3b143657c8479dfc80f032ad2f4000ca468a1.
def localCycle00147 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 19 0, .triangle 31 0, .triangle 12 0, .triangle 2 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint db5a1c72858fd07338f3c97b051312e5f6200c5d2128ca58095decd9616958b6.
def localCycle00148 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3]
    constant := ![-2, 0, -2, -1, -1, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 23 1, .gapLower 1 3, .triangle 3 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint dc235216e43350e084afd14bc459c6b7cbbff7f70621c52ca5de41e943290923.
def localCycle00149 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint dc92a4da6396ae359fa535b0543e924beac723b9423b566f58087426da6fc5f7.
def localCycle00150 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint de21af72db0aff2f89963386277e006ccd044073e17a508aaf39fe8774024f8c.
def localCycle00151 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, -1, 0, -1, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 21 0, .triangle 32 1, .triangle 9 0, .gapLower 0 2, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint e05f9719321dd5e271fe031ed3bb137f92b7c8a4acff3226a75302dea0066629.
def localCycle00152 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 9 0, .gapLower 0 2, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3]

-- Cycle fingerprint e3a1a8c419993d260f255ad0b31e7b32e134cef640df54f0f257a2a9f2ea997d.
def localCycle00153 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 12 0, .triangle 2 1, .triangle 0 0, .triangle 18 0, .triangle 27 1, .corridorLower 3 6]

-- Cycle fingerprint e5b377f9776cb84f16b5904cc88165dfcc32d114d825a653c5ebed61189d4478.
def localCycle00154 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint e659dc187a847c16ec0997e63a8765eea5c3150ddbc2cdb7d268473424291531.
def localCycle00155 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -1, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .triangle 4 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint e6ef9f0fc54444e1d10a3503b14e2648abf292f760b342b4748fc3aafd3f32d8.
def localCycle00156 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![-2, -2, -1, -1, -1, 4, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .triangle 3 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint e9462039f14e42c76a6dc4a3903718ad9cb9f941ace9fc5cacf719b7dfffb8a7.
def localCycle00157 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 33 0, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint e9aae62e99bafc7f4f2ed2215aa3238fd46fd09e3bb85ae211a1cdd18cb7d6aa.
def localCycle00158 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 13 0, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint ecef83f77716124cea3bff2a443ab857e8c464e1b44407ba36f6e9fc7bea6dbc.
def localCycle00159 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 33 0, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint ed742defffd58901cf9a2a0eb7ca8860b46319c8aaaf2cde73469a98bdb6906e.
def localCycle00160 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 3 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint ef24384b2a9da96fd81c953497e7c6f3c4fe67e68c926064135903f9cfd05ec7.
def localCycle00161 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -3, -1, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .triangle 4 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint ef2d70762d4cfcc08590e3a30efe2cde176095f5fd83bad2f9d9b417f3b6a876.
def localCycle00162 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![0, 2, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, false, false, false, true, true] }
  origin := ![.triangle 0 2, .gapUpper 2 2, .triangle 18 2, .triangle 23 1, .triangle 32 0, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 1 1]

-- Cycle fingerprint f150b1fc1433ae759aae0332701eabecfcbc83a841a621cd4b309559c2429bd6.
def localCycle00163 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint f1d6ec30046879e72282fe4b4ecf0fa8eb8086e81042836e31227bc34d33c121.
def localCycle00164 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint f1dc8af48f987f90266a0a3a7c3b8fe4d2599456d8f092c234a5254a490ce91a.
def localCycle00165 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint f4d234be8a632038f0ec95852f84a91ceaaa4f5197fb9bc96780d62a8b33304e.
def localCycle00166 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 32 1, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint f7e80fbc93c590e2b47602093734c52e6de60ca8db81a1f0c4caaece90e917c5.
def localCycle00167 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 12 0, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint f811e9720b21bf20855b4b453d141439dc100bab118dffc3a65b4d4599d051ad.
def localCycle00168 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint f8956432bf5bb39f46ca001fc8d2ac149f57409128b6660f15c7c81325008600.
def localCycle00169 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint fb21f9076743db575fbeff52e51cc6e09bdd094ea489610b002587aa684b54a6.
def localCycle00170 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6]
    constant := ![0, -1, 0, -1, -1, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 32 2, .triangle 21 0, .gapLower 1 4, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0]

-- Cycle fingerprint fcd8255100987d3120209be990b896343a2c6b74907d9b579e4adb30ad9e5ec3.
def localCycle00171 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 19 2, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint fddd90d4596465193b06ee2dd1b41d281c11462154ddc1ed0f77d65a09f5ef11.
def localCycle00172 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4]
    constant := ![-1, -1, -1, 3, 0, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.triangle 23 0, .triangle 32 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .gapLower 1 4]

-- Cycle fingerprint fdfc4e2ea8cec3a98bb8ff88b6866ca1c4540ba43d381850630b98bc339ce2d2.
def localCycle00173 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint fee19ca4f8e6fda5ac6cbbd75e5a8b4a1dcd5afb2ff7d1a69168f4e0bd2dacc5.
def localCycle00174 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 6]
    constant := ![-2, -1, -1, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .triangle 21 2]

def library : Library := fun id => if id < 87 then (if id < 43 then (if id < 21 then (if id < 10 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 7 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))))) else (if id < 15 then (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)))) else (if id < 18 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none))) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)))))) else (if id < 32 then (if id < 26 then (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)))) else (if id < 29 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none))) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none))))) else (if id < 37 then (if id < 34 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none)))) else (if id < 40 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none))) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none))))))) else (if id < 65 then (if id < 54 then (if id < 48 then (if id < 45 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none)) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)))) else (if id < 51 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none))) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none))))) else (if id < 59 then (if id < 56 then (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none)))) else (if id < 62 then (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none))) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)))))) else (if id < 76 then (if id < 70 then (if id < 67 then (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)))) else (if id < 73 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none))) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none))))) else (if id < 81 then (if id < 78 then (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)))) else (if id < 84 then (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none))) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)))))))) else (if id < 131 then (if id < 109 then (if id < 98 then (if id < 92 then (if id < 89 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)))) else (if id < 95 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none))) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none))))) else (if id < 103 then (if id < 100 then (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none)) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)))) else (if id < 106 then (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none))) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)))))) else (if id < 120 then (if id < 114 then (if id < 111 then (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)))) else (if id < 117 then (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none))) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none))))) else (if id < 125 then (if id < 122 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)))) else (if id < 128 then (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none))) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none))))))) else (if id < 153 then (if id < 142 then (if id < 136 then (if id < 133 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none)) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none)))) else (if id < 139 then (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none))) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none))))) else (if id < 147 then (if id < 144 then (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none)) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none)))) else (if id < 150 then (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none))) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none)))))) else (if id < 164 then (if id < 158 then (if id < 155 then (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none)) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none)))) else (if id < 161 then (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none))) else (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none))))) else (if id < 169 then (if id < 166 then (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none)) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none)))) else (if id < 172 then (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id = 171 then some localCycle00171 else none))) else (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 6, 5], ![1, 0, 6, 5, 4, 3], ![0, 4, 1, 6, 5, 2], ![0, 3, 1, 6, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 1, 3, 4, 2]], proof := .tail 79 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13056)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 6, 3, 5], ![1, 0, 6, 5, 4, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 1, 6, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 3, 1, 4, 2]], proof := .tail 166 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13057)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 4, 3, 5], ![1, 0, 6, 5, 4, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 6, 1, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 3, 4, 1, 2]], proof := .tail 172 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13058)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 4, 3, 5], ![1, 0, 6, 5, 4, 3], ![0, 6, 4, 1, 5, 2], ![0, 6, 3, 1, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 4, 3, 1, 2]], proof := .tail 160 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13059)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 4, 3, 6, 5], ![1, 0, 6, 5, 4, 3], ![0, 4, 1, 6, 5, 2], ![0, 3, 1, 6, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 1, 3, 4, 2]], proof := .tail 79 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13060)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 4, 6, 3, 5], ![1, 0, 6, 5, 4, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 1, 6, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 3, 1, 4, 2]], proof := .tail 166 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13061)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 6, 4, 3, 5], ![1, 0, 6, 5, 4, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 6, 1, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 3, 4, 1, 2]], proof := .tail 172 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13062)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 6, 4, 3, 5], ![1, 0, 6, 5, 4, 3], ![0, 6, 4, 1, 5, 2], ![0, 6, 3, 1, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 4, 3, 1, 2]], proof := .tail 26 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13063)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![2, 1, 3, 6, 4, 5], ![2, 0, 6, 4, 3, 5], ![1, 0, 6, 5, 4, 3], ![0, 6, 4, 1, 5, 2], ![6, 0, 3, 1, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 4, 0, 3, 1, 2]], proof := .tail 67 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13064)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![2, 1, 6, 3, 4, 5], ![2, 0, 6, 4, 3, 5], ![1, 0, 6, 5, 4, 3], ![6, 0, 4, 1, 5, 2], ![6, 0, 3, 1, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 116 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13065)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![2, 6, 1, 3, 4, 5], ![2, 6, 0, 4, 3, 5], ![1, 0, 6, 5, 4, 3], ![6, 0, 4, 1, 5, 2], ![6, 0, 3, 1, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 116 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13066)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![6, 2, 1, 3, 4, 5], ![2, 6, 0, 4, 3, 5], ![1, 6, 0, 5, 4, 3], ![6, 0, 4, 1, 5, 2], ![6, 0, 3, 1, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 116 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13067)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![6, 2, 1, 3, 4, 5], ![6, 2, 0, 4, 3, 5], ![6, 1, 0, 5, 4, 3], ![6, 0, 4, 1, 5, 2], ![6, 0, 3, 1, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 4 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13068)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 4, 5, 3, 6], ![0, 4, 5, 1, 2, 6], ![0, 3, 1, 2, 5, 6], ![0, 3, 1, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 45 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13069)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 4, 5, 3, 6], ![0, 4, 5, 1, 2, 6], ![0, 3, 1, 2, 6, 5], ![0, 3, 1, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 28 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13070)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 4, 5, 6, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 1, 2, 5, 6], ![0, 3, 1, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 98 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13071)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 4, 5, 6, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 1, 2, 6, 5], ![0, 3, 1, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 98 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13072)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 4, 6, 5, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 1, 2, 6, 5], ![0, 3, 1, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 65 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13073)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 6, 4, 5, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 1, 6, 2, 5], ![0, 3, 1, 6, 2, 4], ![0, 1, 3, 5, 4, 2]], proof := .tail 120 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13074)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 5, 6, 3], ![1, 0, 4, 5, 6, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 1, 2, 5, 6], ![0, 3, 1, 2, 4, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 23 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13075)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 5, 6, 3], ![1, 0, 4, 5, 6, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 1, 2, 6, 5], ![0, 3, 1, 2, 6, 4], ![0, 3, 1, 2, 5, 4]], proof := .tail 89 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13076)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 5, 6, 3], ![1, 0, 4, 6, 5, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 1, 2, 6, 5], ![0, 3, 1, 6, 2, 4], ![0, 3, 1, 5, 2, 4]], proof := .tail 39 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13077)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 6, 5, 3], ![1, 0, 4, 6, 5, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 1, 2, 6, 5], ![0, 3, 6, 1, 2, 4], ![0, 3, 5, 1, 2, 4]], proof := .tail 7 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13078)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 6, 5, 3], ![1, 0, 4, 6, 5, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 1, 2, 6, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 3, 1, 2, 4]], proof := .tail 157 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13079)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 5, 6, 3], ![1, 0, 6, 4, 5, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 1, 6, 2, 5], ![0, 3, 1, 6, 2, 4], ![0, 3, 1, 5, 4, 2]], proof := .tail 139 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13080)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 6, 5, 3], ![1, 0, 6, 4, 5, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 1, 6, 2, 5], ![0, 3, 6, 1, 2, 4], ![0, 3, 5, 1, 4, 2]], proof := .tail 131 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13081)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 6, 5, 3], ![1, 0, 6, 4, 5, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 1, 6, 2, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 3, 1, 4, 2]], proof := .tail 139 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13082)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 6, 1, 2, 5], ![0, 3, 6, 1, 2, 4], ![0, 3, 5, 4, 1, 2]], proof := .tail 173 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13083)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 1, 2, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 3, 4, 1, 2]], proof := .tail 173 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13084)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 1, 2, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 4, 3, 1, 2]], proof := .tail 93 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13085)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 4, 6, 5, 3], ![1, 0, 4, 6, 5, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 1, 2, 6, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 3, 1, 2, 4]], proof := .low (![1, 46, 19, 90, 161, 140, 48, 152, 31, 128, 125, 82, 132, 75, 27, 51, 117, 11, 10, 60, 34, 106, 94, 33, 119, 17, 92, 63]) }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13086)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 4, 6, 5, 3], ![1, 0, 6, 4, 5, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 1, 6, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 3, 1, 4, 2]], proof := .tail 139 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13087)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 1, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 3, 4, 1, 2]], proof := .tail 173 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13088)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 1, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 4, 3, 1, 2]], proof := .tail 12 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13089)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![2, 1, 3, 6, 4, 5], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![0, 6, 4, 5, 1, 2], ![6, 0, 3, 1, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 4, 0, 3, 1, 2]], proof := .tail 169 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13090)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![2, 1, 6, 3, 4, 5], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 1, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 4, 3, 0, 1, 2]], proof := .tail 74 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13091)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![2, 6, 1, 3, 4, 5], ![2, 6, 0, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 1, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 74 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13092)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![6, 2, 1, 3, 4, 5], ![2, 6, 0, 4, 5, 3], ![1, 6, 0, 4, 5, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 1, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 165 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13093)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![6, 2, 1, 3, 4, 5], ![6, 2, 0, 4, 5, 3], ![6, 1, 0, 4, 5, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 1, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 24 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13094)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 5, 4, 3, 6], ![0, 4, 5, 1, 2, 6], ![0, 3, 1, 5, 2, 6], ![0, 3, 1, 4, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 124 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13095)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 5, 4, 6, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 1, 5, 2, 6], ![0, 3, 1, 4, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 124 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13096)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 5, 6, 4, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 1, 5, 6, 2], ![0, 3, 1, 4, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 141 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13097)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 6, 5, 4, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 1, 5, 6, 2], ![0, 3, 1, 4, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 5 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13098)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 6, 5, 4, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 1, 6, 5, 2], ![0, 3, 1, 6, 4, 2], ![0, 1, 3, 5, 4, 2]], proof := .tail 35 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13099)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 5, 6, 3], ![1, 0, 5, 4, 6, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 1, 5, 2, 6], ![0, 3, 1, 4, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 124 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13100)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 5, 6, 3], ![1, 0, 5, 6, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 1, 5, 6, 2], ![0, 3, 1, 4, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 44 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13101)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 5, 6, 3], ![1, 0, 6, 5, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 1, 5, 6, 2], ![0, 3, 1, 4, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 5 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13102)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 5, 6, 3], ![1, 0, 6, 5, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 1, 6, 5, 2], ![0, 3, 1, 6, 4, 2], ![0, 3, 1, 5, 4, 2]], proof := .tail 76 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13103)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 6, 5, 3], ![1, 0, 6, 5, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 1, 6, 5, 2], ![0, 3, 6, 1, 4, 2], ![0, 3, 5, 1, 4, 2]], proof := .tail 70 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13104)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 6, 5, 3], ![1, 0, 6, 5, 4, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 1, 6, 5, 2], ![0, 6, 3, 1, 4, 2], ![0, 5, 3, 1, 4, 2]], proof := .tail 159 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13105)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 6, 1, 5, 2], ![0, 3, 6, 1, 4, 2], ![0, 3, 5, 4, 1, 2]], proof := .tail 163 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13106)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 1, 5, 2], ![0, 6, 3, 1, 4, 2], ![0, 5, 3, 4, 1, 2]], proof := .tail 163 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13107)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 1, 5, 2], ![0, 6, 3, 1, 4, 2], ![0, 5, 4, 3, 1, 2]], proof := .tail 158 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13108)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 4, 6, 5, 3], ![1, 0, 6, 5, 4, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 1, 6, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 0, 3, 1, 4, 2]], proof := .tail 101 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13109)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 1, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 0, 3, 4, 1, 2]], proof := .tail 163 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13110)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 1, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 0, 4, 3, 1, 2]], proof := .tail 158 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13111)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![2, 1, 3, 6, 4, 5], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![0, 6, 4, 5, 1, 2], ![6, 0, 3, 1, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 4, 0, 3, 1, 2]], proof := .tail 95 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13112)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![2, 1, 6, 3, 4, 5], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 1, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 54 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13113)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![2, 6, 1, 3, 4, 5], ![2, 6, 0, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 1, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 54 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13114)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![6, 2, 1, 3, 4, 5], ![2, 6, 0, 4, 5, 3], ![1, 6, 0, 5, 4, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 1, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 54 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13115)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![6, 2, 1, 3, 4, 5], ![6, 2, 0, 4, 5, 3], ![6, 1, 0, 5, 4, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 1, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 84 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13116)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 5, 4, 3, 6], ![0, 4, 5, 1, 2, 6], ![0, 3, 5, 1, 2, 6], ![0, 3, 4, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 149 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13117)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 5, 4, 6, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 5, 1, 2, 6], ![0, 3, 4, 1, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 9 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13118)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 5, 6, 4, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 5, 1, 6, 2], ![0, 3, 4, 1, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 170 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13119)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 6, 5, 4, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 5, 1, 6, 2], ![0, 3, 4, 1, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 57 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13120)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 4, 6, 3], ![1, 0, 5, 4, 6, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 1, 2, 6], ![0, 3, 4, 1, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 149 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13121)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 4, 6, 3], ![1, 0, 5, 6, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 1, 6, 2], ![0, 3, 4, 1, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 20 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13122)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 4, 6, 3], ![1, 0, 6, 5, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 1, 6, 2], ![0, 3, 4, 1, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 57 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13123)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 6, 1, 2], ![0, 3, 4, 1, 2, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 53 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13124)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 6, 1, 2], ![0, 3, 4, 1, 6, 2], ![0, 3, 4, 1, 5, 2]], proof := .tail 59 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13125)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 6, 1, 2], ![0, 3, 4, 6, 1, 2], ![0, 3, 4, 5, 1, 2]], proof := .tail 107 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13126)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 6, 5, 1, 2], ![0, 3, 6, 4, 1, 2], ![0, 3, 5, 4, 1, 2]], proof := .tail 118 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13127)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 5, 1, 2], ![0, 6, 3, 4, 1, 2], ![0, 5, 3, 4, 1, 2]], proof := .tail 40 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13128)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 5, 1, 2], ![0, 6, 3, 4, 1, 2], ![0, 5, 4, 3, 1, 2]], proof := .tail 130 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13129)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 5, 1, 2], ![6, 0, 3, 4, 1, 2], ![5, 0, 3, 4, 1, 2]], proof := .tail 43 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13130)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 5, 1, 2], ![6, 0, 3, 4, 1, 2], ![5, 0, 4, 3, 1, 2]], proof := .tail 130 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13131)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![2, 1, 3, 6, 4, 5], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 6, 4, 5, 1, 2], ![6, 0, 3, 5, 1, 2], ![6, 0, 3, 4, 1, 2], ![5, 4, 0, 3, 1, 2]], proof := .tail 47 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13132)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![2, 1, 6, 3, 4, 5], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 5, 1, 2], ![6, 0, 3, 4, 1, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 30 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13133)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![2, 6, 1, 3, 4, 5], ![2, 6, 0, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 5, 1, 2], ![6, 0, 3, 4, 1, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 30 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13134)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![6, 2, 1, 3, 4, 5], ![2, 6, 0, 5, 4, 3], ![1, 6, 0, 5, 4, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 5, 1, 2], ![6, 0, 3, 4, 1, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 30 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13135)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![6, 2, 1, 3, 4, 5], ![6, 2, 0, 5, 4, 3], ![6, 1, 0, 5, 4, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 5, 1, 2], ![6, 0, 3, 4, 1, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 49 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13136)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 5, 4, 3, 6], ![0, 5, 4, 1, 2, 6], ![0, 5, 3, 1, 2, 6], ![0, 4, 3, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 168 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13137)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 5, 4, 6, 3], ![0, 5, 4, 1, 6, 2], ![0, 5, 3, 1, 2, 6], ![0, 4, 3, 1, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 147 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13138)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 5, 6, 4, 3], ![0, 5, 4, 1, 6, 2], ![0, 5, 3, 1, 6, 2], ![0, 4, 3, 1, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 25 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13139)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 6, 5, 4, 3], ![0, 5, 4, 1, 6, 2], ![0, 5, 3, 1, 6, 2], ![0, 4, 3, 1, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 143 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13140)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 4, 6, 3], ![1, 0, 5, 4, 6, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 1, 2, 6], ![0, 4, 3, 1, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 71 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13141)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 4, 6, 3], ![1, 0, 5, 6, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 1, 6, 2], ![0, 4, 3, 1, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 145 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13142)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 4, 6, 3], ![1, 0, 6, 5, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 1, 6, 2], ![0, 4, 3, 1, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 115 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13143)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 6, 1, 2], ![0, 4, 3, 1, 2, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 15 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13144)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 6, 1, 2], ![0, 4, 3, 1, 6, 2], ![0, 3, 4, 1, 5, 2]], proof := .tail 162 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13145)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 6, 1, 2], ![0, 4, 3, 6, 1, 2], ![0, 3, 4, 5, 1, 2]], proof := .tail 87 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13146)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![0, 5, 6, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 3, 1, 2, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 55 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13147)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 5, 6, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 3, 1, 6, 2], ![0, 4, 3, 1, 5, 2]], proof := .tail 50 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13148)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 5, 6, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 3, 6, 1, 2], ![0, 4, 3, 5, 1, 2]], proof := .tail 133 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13149)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 6, 3, 1, 2], ![0, 4, 5, 3, 1, 2]], proof := .tail 167 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13150)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![0, 6, 5, 3, 1, 2], ![0, 6, 4, 3, 1, 2], ![0, 5, 4, 3, 1, 2]], proof := .tail 112 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13151)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![0, 6, 5, 3, 1, 2], ![6, 0, 4, 3, 1, 2], ![5, 0, 4, 3, 1, 2]], proof := .tail 3 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13152)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![2, 1, 3, 6, 4, 5], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![6, 0, 5, 3, 1, 2], ![6, 0, 4, 3, 1, 2], ![5, 4, 0, 3, 1, 2]], proof := .tail 121 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13153)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![2, 1, 6, 3, 4, 5], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![6, 0, 5, 4, 1, 2], ![6, 0, 5, 3, 1, 2], ![6, 0, 4, 3, 1, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 121 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13154)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![2, 6, 1, 3, 4, 5], ![2, 6, 0, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![6, 0, 5, 4, 1, 2], ![6, 0, 5, 3, 1, 2], ![6, 0, 4, 3, 1, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 80 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13155)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![6, 2, 1, 3, 4, 5], ![2, 6, 0, 5, 4, 3], ![1, 6, 0, 5, 4, 3], ![6, 0, 5, 4, 1, 2], ![6, 0, 5, 3, 1, 2], ![6, 0, 4, 3, 1, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 91 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13156)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![6, 2, 1, 3, 4, 5], ![6, 2, 0, 5, 4, 3], ![6, 1, 0, 5, 4, 3], ![6, 0, 5, 4, 1, 2], ![6, 0, 5, 3, 1, 2], ![6, 0, 4, 3, 1, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 153 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13157)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 5, 4, 3, 6], ![0, 5, 4, 1, 2, 6], ![5, 0, 3, 1, 2, 6], ![4, 0, 3, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 6 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13158)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 5, 4, 6, 3], ![0, 5, 4, 1, 6, 2], ![5, 0, 3, 1, 2, 6], ![4, 0, 3, 1, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 136 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13159)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 5, 6, 4, 3], ![0, 5, 4, 1, 6, 2], ![5, 0, 3, 1, 6, 2], ![4, 0, 3, 1, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 105 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13160)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 6, 5, 4, 3], ![0, 5, 4, 1, 6, 2], ![5, 0, 3, 1, 6, 2], ![4, 0, 3, 1, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 52 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13161)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 4, 6, 3], ![1, 0, 5, 4, 6, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 1, 2, 6], ![4, 0, 3, 1, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .low (![32, 81, 58, 62, 85, 154, 100, 86, 164, 111, 113, 13, 151, 103, 109, 36, 56, 104, 41, 88, 16, 66, 146, 148, 96, 2, 174, 61]) }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13162)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 4, 6, 3], ![1, 0, 5, 6, 4, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 1, 6, 2], ![4, 0, 3, 1, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 14 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13163)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 4, 6, 3], ![1, 0, 6, 5, 4, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 1, 6, 2], ![4, 0, 3, 1, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 102 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13164)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 0, 3, 1, 2, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 142 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13165)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 0, 3, 1, 6, 2], ![0, 3, 4, 1, 5, 2]], proof := .tail 73 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13166)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 0, 3, 6, 1, 2], ![0, 3, 4, 5, 1, 2]], proof := .tail 64 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13167)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 0, 3, 1, 2, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 37 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13168)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 0, 3, 1, 6, 2], ![0, 4, 3, 1, 5, 2]], proof := .tail 37 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13169)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 0, 3, 6, 1, 2], ![0, 4, 3, 5, 1, 2]], proof := .tail 37 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13170)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 0, 6, 3, 1, 2], ![0, 4, 5, 3, 1, 2]], proof := .tail 0 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13171)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 3, 1, 2, 6], ![4, 0, 3, 1, 2, 5]], proof := .low (![138, 22, 58, 72, 114, 129, 42, 126, 164, 108, 155, 97, 122, 18, 77, 110, 78, 99, 150, 29, 127, 171, 156, 134, 69, 135, 8, 68]) }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13172)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 5, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 3, 1, 6, 2], ![4, 0, 3, 1, 5, 2]], proof := .tail 123 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13173)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 3, 6, 1, 2], ![4, 0, 3, 5, 1, 2]], proof := .tail 64 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13174)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 6, 3, 1, 2], ![4, 0, 5, 3, 1, 2]], proof := .tail 21 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13175)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![2, 1, 3, 6, 5, 4], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 0, 3, 1, 2], ![4, 5, 0, 3, 1, 2]], proof := .tail 21 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13176)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![2, 1, 3, 6, 5, 4], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 0, 3, 1, 2], ![5, 4, 0, 3, 1, 2]], proof := .tail 144 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13177)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![2, 1, 6, 3, 5, 4], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![6, 0, 5, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 0, 3, 1, 2], ![4, 5, 3, 0, 1, 2]], proof := .tail 137 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13178)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![2, 1, 6, 3, 5, 4], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![6, 0, 5, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 0, 3, 1, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 83 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13179)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![2, 6, 1, 3, 5, 4], ![2, 6, 0, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![6, 0, 5, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 0, 3, 1, 2], ![4, 5, 3, 1, 0, 2]], proof := .tail 137 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13180)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 2, 1, 3, 5, 4], ![2, 6, 0, 5, 4, 3], ![1, 6, 0, 5, 4, 3], ![6, 0, 5, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 0, 3, 1, 2], ![4, 5, 3, 1, 2, 0]], proof := .tail 137 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13181)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 2, 1, 3, 5, 4], ![6, 2, 0, 5, 4, 3], ![6, 1, 0, 5, 4, 3], ![6, 0, 5, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 0, 3, 1, 2], ![4, 5, 3, 2, 1, 0]], proof := .tail 38 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13182)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![2, 6, 1, 3, 5, 4], ![2, 6, 0, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![6, 0, 5, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 0, 3, 1, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 83 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13183)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (13056 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 13056 ≤ id.val) (hhigh : id.val < 13184) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 13056)) = true := by
  let j : Fin 128 := ⟨id.val - 13056, by omega⟩
  have hsum : 13056 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (13056 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard102
