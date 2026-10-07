import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard142
open N4R2OuterLeftReplay

-- Cycle fingerprint 00ca837f382f688cc15514a55c47cbff4b85169f511e464240173ecbf03c4802.
def localCycle00000 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, 0, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4]

-- Cycle fingerprint 021918251da06249e0f771a031c37ac25982747d0058b03b05f1a54baf2eb4ef.
def localCycle00001 : Cycle where
  length := 11
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6]
    constant := ![0, 0, -1, -1, 0, -1, -3, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 023e3adbe0a5716e9a29e5b6468b42f7f9f051a03d7359dc73b5119348a26270.
def localCycle00002 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 4, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 3 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 028dc305099b46b22f57bef485b56fe38b4307d5e49dacacd9ad5057c34c5de3.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6]
    constant := ![-1, -3, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0]

-- Cycle fingerprint 0320891b2c4b72737927a099d7820214963509164d5f2817058cf9690a23dbb5.
def localCycle00004 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 04373a79f6706e0195394c930851c25c3d658572218deb045f78375944da66e2.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .triangle 19 0, .gapLower 3 0]

-- Cycle fingerprint 07a978c3c9c6183724e92af296a2ea282f69eb273b55865f202306c04c1e2a54.
def localCycle00006 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 2]

-- Cycle fingerprint 086fae9efce582a1683bdcef7bd91b027f8070895e821c8c0845cf5661e5921e.
def localCycle00007 : Cycle where
  length := 6
  data := {
    node := ![.distance 4 5, .theta 4, .zero, .theta 6, .distance 1 6, .distance 1 4, .distance 4 5]
    constant := ![-1, 0, 0, 2, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 4 5, .thetaLower 4, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 22 0]

-- Cycle fingerprint 0a61cf99068cb04a9e050735b0ce46281b72aa2a781cc71b778e6369b4f9d6f7.
def localCycle00008 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 2, .triangle 9 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 0a7f3952644571b5e57fc0145e83ae4382a84f5283206e3d624f4490282d0b7d.
def localCycle00009 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, 0, -1, -1, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 0ca71ecb0ccf6c2ede176396b2fb83276c0d85cee02d4509b71ad79ed0e31635.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 3, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 20 0, .gapLower 3 0]

-- Cycle fingerprint 0dc4696db5bbaf961a9c93dd71f69882c8e8d0ca7d081b96a2bf8200111b6f21.
def localCycle00011 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4]
    constant := ![-1, -2, -2, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0]

-- Cycle fingerprint 0ea362712132662063765c868f269267ac52261bd266d1205f027528a045ee83.
def localCycle00012 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 0, .gapLower 3 0]

-- Cycle fingerprint 0ed49104349d1b445bf0c026c8fa3fe81e2aa0a1477c0d74fa8393d9c83e9472.
def localCycle00013 : Cycle where
  length := 15
  data := {
    node := ![.distance 1 4, .distance 4 5, .theta 4, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, 0, -1, -1, -1, 0, -1, 3, -3, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 22 0, .corridorLower 4 5, .thetaLower 4, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint 13535f99b105865a8ff3e765a76cb48427542d979ee7df6d6b8854981fba1515.
def localCycle00014 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 1394b105fdbbc1cdcb82d2c56a3873339e28e8baff651a3cff3c734da795cf19.
def localCycle00015 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 1457feb3b15b35239d0c9ba9beb9d997760b03faee0fbb2e876dfb2fa74fa520.
def localCycle00016 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 2 3, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 5, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, 0, -1, 0, -2, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.triangle 26 0, .triangle 5 2, .triangle 11 0, .triangle 21 2, .gapLower 1 4, .gapLower 5 0, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 14a9803b9e46a0c197c433a93b04d45c24fc5e635258914fea426660d63fbff4.
def localCycle00017 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 182fefa0aa6b2acd24feb5008e1d75924190ed0458241704193d37edf13f87d0.
def localCycle00018 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 1 5, .distance 1 3, .distance 3 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 2, .gapLower 1 2, .gapUpper 3 1]

-- Cycle fingerprint 195be1b48aa6290b889b664d65a2459be4f142f6536b3f7ef7e12d0a8923af58.
def localCycle00019 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 5, .corridorUpper 0 1]

-- Cycle fingerprint 197436fc45550d911832764fcb0032760440844294736f051840e1571c46ebfa.
def localCycle00020 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 22 0, .triangle 23 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 1b4315f4a9f6d6f352fca5fa0cdb1e1462af6701c7d2249cd744a9226bb96d95.
def localCycle00021 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 5, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 5, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint 1c5fc281fb9c64e56e6bd8af894a8175d2055eca18285c82476f519fbbf05da7.
def localCycle00022 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 1ccd9a0ba815cf2714d88025b3b62c6affac4dbdf44cc5b0a5febf9689d7ce49.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, -1, 0, -2, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 1d5dba362aec434349059cf32c4c865958a66c8c60567081671fa3fd21267c21.
def localCycle00024 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 2, 0, 0, -1, 0, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 3 2, .triangle 10 1, .triangle 11 0, .triangle 21 2, .triangle 23 1, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 1efd4bca441f19f38f40a6f8b859e4c23af5d524e140cd86303f7a49f473ad7a.
def localCycle00025 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5]
    constant := ![-1, -1, -1, 0, -1, 0, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2]

-- Cycle fingerprint 1f9605a5658cac83979b17c6eb4b91473a88e05a7f4f2c4fe53f34702059b7dd.
def localCycle00026 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 10 0, .triangle 9 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 2087218ff811b62bf0a1b997503ea153bc7155a81ea56c0022a2ab2f0578fae1.
def localCycle00027 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 4, .distance 1 3, .distance 3 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 1, .gapLower 1 2, .gapUpper 3 1]

-- Cycle fingerprint 231b708a381e2354bd92fbf338b90fe458446c17b4ab2ae495b68d1ef77506fd.
def localCycle00028 : Cycle where
  length := 12
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3]
    constant := ![0, -1, 0, 0, 3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 20 0]

-- Cycle fingerprint 24b3fdf520bc75a805f1955d0e50b2de5ae4dec229892a6ff6215e3e1f8a9e28.
def localCycle00029 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 0, .triangle 5 2, .triangle 9 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 25176d0e917e2ceb2a2408158a8dc5fe89d8339f7d645e40082dd3498b26709c.
def localCycle00030 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6]
    constant := ![-2, 0, -2, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .triangle 17 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 2]

-- Cycle fingerprint 265286f33e94e8d1084daa31fa5ef40991ba6de8e52eaf39d9d82c3f7e0f2190.
def localCycle00031 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![0, 0, -1, 3, 0, -1, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, true, false, false, false] }
  origin := ![.triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint 269dbd2c83d51d931bfa65c412c60a0b4c507ed6c388dac68ccd221415fa7631.
def localCycle00032 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -1, -1, 0, -2, 3, -2, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 10 0, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 27621354d6fee523d55668476077b06de6f975dcb2a5c7f2e550e153cfbf5d46.
def localCycle00033 : Cycle where
  length := 12
  data := {
    node := ![.distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 5 2, .triangle 9 0, .triangle 19 0, .gapLower 1 1]

-- Cycle fingerprint 2bbd1d48d3b73fa3239f6053e5ee1f43c0135cbfc252f3ef33e75b3b381131e8.
def localCycle00034 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 2d601433b3bfc6df06ecae2744778b950e75edc473a9d720b79eb726270323c6.
def localCycle00035 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 10 0, .triangle 9 0, .triangle 19 2, .triangle 23 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 2e10fb6da56a12c33421a171e639b0f05716cfdaa14e453bb9c9aae5f664539b.
def localCycle00036 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 33 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .triangle 19 0, .gapLower 3 0]

-- Cycle fingerprint 3061cd84517185cfe1442884fd8c2359c03ea01178b6ae2f8296338e0ef5ab83.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6]
    constant := ![-1, -2, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0]

-- Cycle fingerprint 314c99d03f7be32bb91bd807ec54e5ab2a0db8bfadc1fd955c25c28b6d66c5da.
def localCycle00038 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 1 4]
    constant := ![0, -1, 0, 0, 3, 0, -1, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 23 0]

-- Cycle fingerprint 324c61adc1c903635ae9d0a82c66207120121939fa76b145e7ef2972f5b2f180.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 2, -3, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 22 1, .triangle 19 1, .triangle 15 1]

-- Cycle fingerprint 33159e843f7c67936d9125707b9b4ea9933ac9517ec119d63e016ba78b49e491.
def localCycle00040 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 33 0, .triangle 10 0, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 33b477789d6e6f91ec809138ed8d02591b80f29906a1e0d74120ef64cca96b87.
def localCycle00041 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 20 0, .gapLower 3 0]

-- Cycle fingerprint 346833298e8e1a15c81fa843e3baa36dac7974f5cee35f5f34247fda7e5640d9.
def localCycle00042 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 3]
    constant := ![0, -3, 0, 0, 3, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 0]

-- Cycle fingerprint 364359bdca56063752587979ae8e8b66baa5f98995b802c3932514482da7a9ab.
def localCycle00043 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-2, 3, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 3a1a72ef6abc6b92be705aca63dd3ccfcd54d375c00a4f0f9e4308054f17e6ed.
def localCycle00044 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 10 0, .triangle 9 2, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 3bb162786982eb1cd10ebfce8c8e8b5dd9843806a9db897009bb79a745b9a1e1.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6]
    constant := ![-1, -1, 0, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 32 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0]

-- Cycle fingerprint 3beee8889fed02e5e6ba9701489db9fbe87a4f219b43a497748d87c837f331af.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6]
    constant := ![-1, -2, -2, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 21 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0]

-- Cycle fingerprint 3c18901d4f5112342afe61e1620eb572eace3472819777c6f38a5105a578d5ec.
def localCycle00047 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 1, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 3cf896383bfdb6afe859a5579988366b77a074fc016309ce257be9a682b35867.
def localCycle00048 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6]
    constant := ![-1, -1, 0, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 32 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0]

-- Cycle fingerprint 4128243682a384336948840d462fb556ba0d31365de798ba76a528fb8ab82492.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 5, .distance 0 3, .distance 3 6]
    constant := ![0, -1, -2, -1, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 33 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 3 2, .triangle 10 1, .triangle 11 0]

-- Cycle fingerprint 41b2387da5d0dcff0240113d79b704339783e4edb59386a312fbb3555572d646.
def localCycle00050 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .corridorLower 3 6]

-- Cycle fingerprint 465f316f4df3cad3526333ad17969a5e9811af7b665dcbd87db4e368f1f6cb06.
def localCycle00051 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6]
    constant := ![-2, 0, -2, -1, 4, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0, .triangle 24 2]

-- Cycle fingerprint 4662926673ba4d2581b94cf00f78647a04c96f5249c91f7140fe82a2b9383a7d.
def localCycle00052 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3]
    constant := ![-1, 0, -1, -2, -1, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 10 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0]

-- Cycle fingerprint 49e0b2ef8401a2804ce90f104119ee07cfd5c84e1322a652a33a1cf8a882f994.
def localCycle00053 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 4a356922d207f0ad48d021b3a255422bc850c3eb70ce6ceec684adf4061dc714.
def localCycle00054 : Cycle where
  length := 10
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 5]
    constant := ![0, -1, 0, -1, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 1, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 10 0]

-- Cycle fingerprint 4c6002733274460b2039ef9aafa73d84e4ba34d81e520bf685487bc8cc27e520.
def localCycle00055 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 5]
    constant := ![0, -1, 0, -1, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, true, true, false] }
  origin := ![.triangle 31 1, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 4 2, .triangle 11 1, .triangle 10 0]

-- Cycle fingerprint 4cfa342924aac7f8bd7a7ec5a51474a9c091aa0540d348034e7f2f6b80ffc84b.
def localCycle00056 : Cycle where
  length := 11
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 6]
    constant := ![3, 0, 0, -1, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 19 2, .gapLower 1 3, .triangle 17 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint 4d8b3af127848d31085b6773f1463fd42ed9608e0a3e7ad8a39cd39e09330102.
def localCycle00057 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, 0, -1, -1, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 4e5139cc2458c58222a220d97b6cad7864c5efa4740e27a58b20a1a4c1c9b926.
def localCycle00058 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .triangle 19 0, .gapLower 3 0]

-- Cycle fingerprint 4e670ad8699b18e95a85dece7c27c065af1438bedd4bfb64befc04fee5f03789.
def localCycle00059 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, -1, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 19 2, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 4f4d367e86815ad3a49638c093f9fb21bec187d8424e01d0598d8bfb2ac5523c.
def localCycle00060 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 6, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![-1, -1, 0, 0, -2, 0, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, true, true] }
  origin := ![.triangle 11 0, .triangle 9 0, .triangle 19 2, .triangle 22 2, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint 50c61c5e20026ced4dbfa5dafa49856f124b0b5cea20b4ef792a854ebe79247c.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 20 0, .gapLower 3 0]

-- Cycle fingerprint 50e67409caac92ebb249db673f3807419b61df1cbf0cff323514ef8e2858c2fa.
def localCycle00062 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![-2, 0, -2, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.gapLower 1 3, .triangle 16 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 52328c7075ee57691571e47a4d63b673c031a706f909aa559459eb3255ee33f9.
def localCycle00063 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint 52515d53cd1e314d50830254f88966acf5a0a0469a8afc817beec53485a771fa.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 0, 2, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 54a548c01dd81cdf698fe5106df2a8ddeead83f7853cfb1ba4503d116073d5fe.
def localCycle00065 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 1, .gapLower 1 4, .gapUpper 5 1]

-- Cycle fingerprint 54f88b6aeb0cf5d0f07ec4e5eb9ffa2280cca691f646d9bb79709b96f5ca392a.
def localCycle00066 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6]
    constant := ![0, -1, 0, -2, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 33 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0]

-- Cycle fingerprint 569e5a51779bf7ee10c1e51f13a870a2d37fe7ff0ff4194f1b0a1ca506480d74.
def localCycle00067 : Cycle where
  length := 10
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6]
    constant := ![0, 0, -1, -1, -1, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 57e116fb4946ca29596ca8d61682c97d467cb6469828953cdc947a04a5ff70ad.
def localCycle00068 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 22 1]

-- Cycle fingerprint 589f5e7a97e34b6dab585454b72d31e3e76fe641f51cf76d19067f10e0d8c84b.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 598293ca09f94b2798cf4db4f6e8b1ab33f327291be3d0dc3e34f5f7481b2273.
def localCycle00070 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 5b98ddfc98ef442a81a78cda18f579801a762c50da4daac9ea58bca87cf903e1.
def localCycle00071 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6]
    constant := ![-2, 0, -2, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint 5c64412bd8e8c1e9eac1034a549588731e23ca6388569b74be279f1f2aa363a2.
def localCycle00072 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![0, -1, -1, 0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 19 2, .gapLower 1 3, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint 5c94931e71fb001eeb92d0a362a035f889280c4606b9b3aeebc3218b3e0d2697.
def localCycle00073 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 2, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 5c96f37054b7bac940bc67395f93a0343906f24aef0015b313d6ef0038777f6e.
def localCycle00074 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint 5e2d439a42e6a78a30d8108c30d2790138eddadaf2aa8967e80152cfc1304027.
def localCycle00075 : Cycle where
  length := 11
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6]
    constant := ![3, 0, 0, -1, -1, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 20 2, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint 5f981b1b24ea8e81fc9f14d69b0790fd4b3e98507c1959fb084eeeae39f4737c.
def localCycle00076 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 5]
    constant := ![0, -1, 0, -1, 1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 31 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 4 2, .triangle 11 1, .triangle 10 0]

-- Cycle fingerprint 5faf6a56e47375b7f82c70c316f2b589b9cefa953682aacb08fde7467b66068b.
def localCycle00077 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 605f5383f9d555a7ca98a22937f7e306850534e820bd27aa16e75107a13cda98.
def localCycle00078 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 5, .theta 1]
    constant := ![2, 0, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 2, .triangle 11 1, .triangle 9 0, .triangle 19 2, .gapLower 1 3, .corridorLower 1 5]

-- Cycle fingerprint 610c16bf824f7c065ea324050076851bf2837bb8c7cb1a2ae844c394e16929f1.
def localCycle00079 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 2, .triangle 23 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 61ca4eda8b223d5b0dd0a7075395b1eada15ff62afd9c1b6ba471f55de6d6123.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 5]
    constant := ![0, -1, 0, -1, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 31 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 4 2, .triangle 11 1, .triangle 10 0]

-- Cycle fingerprint 6227cf9115d0abb366cfc17ca8e0f83eb2706aa37f93917539f6fb858e6c9480.
def localCycle00081 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .distance 1 3, .theta 3, .distance 2 3, .distance 3 5]
    constant := ![-1, -1, 0, -1, -1, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 33 0, .triangle 14 0, .gapLower 0 3, .triangle 9 0, .triangle 19 0, .gapLower 3 0, .corridorUpper 2 3, .triangle 26 0]

-- Cycle fingerprint 63df17bfb50ce0dc2b0835f29b81535ea36e4acd674f6d4097e46f177eca68d5.
def localCycle00082 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3]
    constant := ![-1, 0, -1, 0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 11 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0]

-- Cycle fingerprint 64f61d124f6de9e8d0f6a34c12a8af017f0944b03dab5d7e97ac653536a57a60.
def localCycle00083 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6]
    constant := ![-3, 0, 0, -1, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2]

-- Cycle fingerprint 65b2d9668972c3f3f4f1c0f601a2d9d03dd60396a2c10c7d6263b6fa9226bd3e.
def localCycle00084 : Cycle where
  length := 13
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 3, .distance 3 6, .distance 3 4, .distance 1 3]
    constant := ![0, -1, 2, -2, -1, -1, 3, 0, -1, 0, -1, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true, false, true, false] }
  origin := ![.triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 2, .triangle 11 0, .triangle 32 1, .triangle 19 0]

-- Cycle fingerprint 66d58de818333d1f8d71a7d5fea4ca0aa9f52cec9d57aeac9a1c907883e7e534.
def localCycle00085 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 3 4]
    constant := ![-1, -1, 0, -1, 0, -1, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.triangle 32 0, .triangle 23 0, .gapLower 1 3, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 25 0]

-- Cycle fingerprint 68656bd4d0caba07966e69f36a766d7588a499bfdd24993cb7b092d7f3f5d70a.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 5]
    constant := ![0, -1, 0, -2, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 31 1, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .gapLower 1 6, .triangle 4 2, .triangle 11 1, .triangle 10 0]

-- Cycle fingerprint 6e506e15f1f8fca3231d521beae0fefd462d8378a355dc89ebe7ca790c077c59.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3]
    constant := ![0, -3, 0, 0, 3, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 19 0]

-- Cycle fingerprint 6e9bc4a71b272a2bfe37d540507bf89b859ad750b16980cb2b3b7802776bd541.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 19 2, .triangle 23 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 70b69b6d91cc882816430128743a443533683fc03ccc838a6e978933669451ef.
def localCycle00089 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .gapLower 3 3, .triangle 10 0, .triangle 20 0, .gapLower 3 0]

-- Cycle fingerprint 71605fcab41abb9cda5b67051e57dcb398a6412dc427e1f9597be8da63c054c4.
def localCycle00090 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, -1, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 2, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 716f1709035af2aa870a88e454bfbd24e3838a1deef682f0af6d870e3cad04a7.
def localCycle00091 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 721f76c79ef057af7c69f17daf93593bf674379d0cbdb488f6985411eb2eac3b.
def localCycle00092 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![2, 0, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 2, .triangle 11 1, .triangle 10 0, .triangle 20 2, .gapLower 1 3, .corridorLower 1 4]

-- Cycle fingerprint 7259d913abf72cf39e13ef91f091ddc0e73ba3cfbd4c0a36d2bd31fc9ebc02a4.
def localCycle00093 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 1, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 72ad5fe18134db3eaa24d81ba9f5ef130368f4fe465353df02da046ee43421ca.
def localCycle00094 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 1 4]
    constant := ![0, 0, 3, -1, -1, -1, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3, .triangle 26 0, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 23 0]

-- Cycle fingerprint 77236d6af1163e1ea58535534ce07fdfffee09cfbbbe836934b4f508a6e1fcbc.
def localCycle00095 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, 0, 0, 2, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 17 1]

-- Cycle fingerprint 777df6efd28f06d7d9f87e111052d60db790b510943340e3c76587de81b269bf.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 4]
    constant := ![0, 0, -2, -1, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, false] }
  origin := ![.triangle 19 2, .triangle 22 2, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 4 2, .triangle 11 1, .triangle 9 0]

-- Cycle fingerprint 77b039111954298f9fb4224d24c051fbaabc990ce3baed90e761b6aa31695e3d.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 3, .distance 3 4, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 2, .triangle 9 0, .triangle 19 2, .triangle 23 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 77ca3b2b6d0cfc7d5217fdee0c02346ac835ede9be684ff260dd2a9ebac8dc12.
def localCycle00098 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-2, 3, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 783c7f2534cf08aa2f71c6dd246efc833ca2e1953cca9e80be11234dccc17338.
def localCycle00099 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 7865079d0f9978b522293128c1f96e31aa2e45db516897c04cffbdc8d930b987.
def localCycle00100 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 2 3, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, 0, -1, 0, -2, -2, -1, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, true, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 26 0, .triangle 5 2, .triangle 11 0, .triangle 21 2, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 78cd706621a5eeec24743466f8a6c82813feb0adf3331f4b6298b648fce12e4d.
def localCycle00101 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -1, -1, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 2, .triangle 11 1, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 78f93dee320114dd2e20e494032a1072c68f84526cb9b8f1784dbece0d6dd55e.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 790155beba51d606bbd95bb1c6e3d0a69a90dce0dacbb173f22328dd26148704.
def localCycle00103 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5]
    constant := ![3, 0, -1, -1, 0, -1, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 7b2011fa748549f54ab8630f02abf00b1e2fce5a727b6635e9ff9a19fb0b57c0.
def localCycle00104 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 8160d3de7e706136b6f820a504dcc8de6e89149d9d0108203e443ce9ecef7561.
def localCycle00105 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .gapLower 3 0]

-- Cycle fingerprint 81f697f4f4fc90ec661407226481ca8f8d3f6eac0b70d38d1a1a0b9195d29f86.
def localCycle00106 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4]

-- Cycle fingerprint 8216c72ff2fa7ecadeec157193df622e76c69ff386054e4f1721d96ceab65331.
def localCycle00107 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 821c469b368a815673218052a0e0d90b120ec19a1caecc4c9dadda45929aba97.
def localCycle00108 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -1, -1, 0, -1, 3, -3, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 10 0, .triangle 11 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 8278cc3000ea73269c33fcc2c373064c3d0c51c339a24a2c59cf45e62726b9c6.
def localCycle00109 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 20 2, .triangle 22 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 85ab792a2d69598de6ef15b0931479ab0e89ee641a2693c9d59e9e4f3d2a190f.
def localCycle00110 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 10 0, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3]

-- Cycle fingerprint 85b4190868325e7b091e8c9f6d7d86419c5996d3d32921365ccc2f4516e0aa99.
def localCycle00111 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, -1, 0, -2, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 14 0, .triangle 24 0, .triangle 22 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint 865415a945298212ee12c9f8691f6fba0f26d27cc3281c7468943d15c4214850.
def localCycle00112 : Cycle where
  length := 11
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3, .theta 1, .zero, .theta 6]
    constant := ![3, 0, 0, -1, -1, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 19 2, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint 865e8986ad0b28caaa8eef2fd0a02ce68175e10e404d75d6cd73830726322678.
def localCycle00113 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3]
    constant := ![-1, 0, -1, 0, -2, 0, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 11 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0]

-- Cycle fingerprint 88e83e5dac24aa6599fc20a66494ff8e025166b9fca095a35eb86bf6905f6c0c.
def localCycle00114 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4]
    constant := ![-1, -3, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0]

-- Cycle fingerprint 8aae63cb1471124b819c54b547fb65538e9e47c9e26a5cc22c719f3c0371ae14.
def localCycle00115 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 6, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![-1, -1, 0, 0, -2, 0, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, true, true] }
  origin := ![.triangle 11 0, .triangle 10 0, .triangle 20 2, .triangle 22 1, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint 8ad561357178897a287700baee930b73ce472c83873091d3841caf8be1ff0950.
def localCycle00116 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-2, 0, 0, 2, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 16 1]

-- Cycle fingerprint 90b71747b3907efa42dc35f5d8b40bcc46cec9b310deab3097205c3be8f4ad42.
def localCycle00117 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 6, .distance 1 6, .distance 1 4, .distance 1 5, .distance 1 3, .theta 1]
    constant := ![0, 0, 0, 2, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 22 2, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 938efa9cd2c4130c5fbac5be372a610ef7d1e3b8f5274141ba466223cf408213.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, -1, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint 93fce1e9aaa66578333bdf97a3d35a5107cceefba31042ea40875d8c17f9bbc2.
def localCycle00119 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 9450cf65a8fc5ce2f64e9b2835240cc8e73d15433e8598dae802616c5bcb18c1.
def localCycle00120 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 0, .triangle 9 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint 955488542f8790f18cd7b1964b7a7aa89a292ef7734eca582d263b201905a3c9.
def localCycle00121 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 20 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 95f71309a3b0906220f5c635ecb7d67f864648b39e1acdddd0c193bc10b3248f.
def localCycle00122 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![2, 0, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 10 1, .triangle 9 0, .triangle 19 2, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 96e99b8e9893184aa35e0f452b764efa1661617418a5bbbc12b6e4f542612dac.
def localCycle00123 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 2, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 977c3aed15571bb0a748f807e5c33035d9299bbf91685a1a82c37e8db7e9fa36.
def localCycle00124 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -1, -1, 0, -1, 3, -3, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 10 0, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 97d98d1c460e5515445fffba4bb8b17cd1593015b38b615950e36d62968f58d4.
def localCycle00125 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3]
    constant := ![0, -1, 0, 0, 3, -1, -1, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 26 1, .triangle 10 0, .triangle 9 0, .triangle 19 0]

-- Cycle fingerprint 987cd865b2f8e5101aef39c932bae36743639d12a54773485805675c2183f73c.
def localCycle00126 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, -1, 0, 0, -1, -1, -1, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 33 2, .triangle 11 0, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 99ba9ea8968fe3f2e294f8669fd42c7bac528c2ef04533dcfca5e724ab55f323.
def localCycle00127 : Cycle where
  length := 11
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6]
    constant := ![0, 0, -1, -1, 0, -1, -2, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 9a1a5ba7ba4f31e05951e1165fe9b735a5e3c34f6afd5fa035e4881f58228c61.
def localCycle00128 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 6, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![-1, -1, 0, 0, -2, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 11 0, .triangle 10 0, .triangle 20 2, .triangle 22 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint 9bd397816e256c00c3d7b3954efd8ffcc99856311beb43032d3eb47b0c0fc85f.
def localCycle00129 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![-3, -1, 4, 0, -1, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint 9d6a20949f31860b67839d3d7aaad17c203f95167ece5dfd15f7c902b9bcc236.
def localCycle00130 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![0, -2, 0, -1, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 9e5d3f9eb9c9bafc73993f979befc5fd584028548dc55c604550d1c48e1d48a3.
def localCycle00131 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![-2, -2, -1, 4, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 9f4e799a136c28548f47097af37bef54762dced50aa15e97ec2986324dae59d8.
def localCycle00132 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 0 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![-1, 2, 0, 0, -1, 0, -1, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.corridorLower 1 3, .gapLower 1 6, .triangle 3 2, .triangle 10 1, .triangle 11 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 9f85de6231f56c4994d7b0a977501ad4b58ed2ea3472bbafc32aafc4a743a6ba.
def localCycle00133 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -1, -1, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 10 1, .triangle 11 0, .triangle 21 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint a0b543c028475e00bb35543c9aab47851100c366945b66dfacf707a747554d2b.
def localCycle00134 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint a0f2d2613b5c3599056a3a88a6e2c6f3b951632ca91a17e091cc64d4d9b3a61c.
def localCycle00135 : Cycle where
  length := 10
  data := {
    node := ![.distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 3 5]
    constant := ![-1, -1, -1, 0, -1, 0, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3, .triangle 26 0]

-- Cycle fingerprint a1a21c7ae1799f39ac354507a2548b30c03d51e8cf9de907c07062de2c81dfaa.
def localCycle00136 : Cycle where
  length := 10
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, -1, -1, 0, -1, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint a2601035bd31534f712076e0fa64b3538d32bf8ecf36befeb4c15c5b7709a115.
def localCycle00137 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4, .distance 4 5]
    constant := ![-1, 0, 0, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 23 1, .triangle 22 0]

-- Cycle fingerprint a5d08cad6102b26cf57eab8a69cdd8c525902cd78d2f7c1cf1a0312f97ae5cc2.
def localCycle00138 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 20 0, .gapLower 3 0]

-- Cycle fingerprint a63033a4a40dbedeacf9014b52ccd90025fc35995b537ff55ca2b08f38ca2b6f.
def localCycle00139 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, -1, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 2, .gapLower 1 4, .triangle 17 1]

-- Cycle fingerprint a7fe4d99e0613f0f20fbfd9025abc36be83f545f35cf86bc7a2c49ea36d36c85.
def localCycle00140 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5]
    constant := ![0, -1, -1, -1, 0, -1, 2, -2, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5]

-- Cycle fingerprint a8a0f38e9928ba6db4aab322cab412736047c05f2beeabdf202eceff1c2ac589.
def localCycle00141 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 2, .gapLower 1 4, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint ab2e431683e33ef5549bd0e26a246d769bc6119c7137cd0c217a10f193f042bd.
def localCycle00142 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 5]
    constant := ![0, 0, -2, -1, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, false] }
  origin := ![.triangle 20 2, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 4 2, .triangle 11 1, .triangle 10 0]

-- Cycle fingerprint abaafa94a9c6047f8e670ccafb4893335e1f42681a02c195a361955d41c9562b.
def localCycle00143 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-1, 4, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 4, .gapLower 1 6, .triangle 3 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint ac9becf17b611cb6097498d8db48743d3de32a8a13e5a3ba6f8700a379898a14.
def localCycle00144 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, -1, -1, 0, -1, 0, -3, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint aed5eb686feccff0b5f2b6edbc5208f29a8d50840dc4b3644a3b35338db84b8f.
def localCycle00145 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 9 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint afb6dc42b41327b83fb9a2dd445fce4cea6df8afe14f850eb038fa14b436b48b.
def localCycle00146 : Cycle where
  length := 12
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3]
    constant := ![0, -1, 0, 0, 3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 19 0]

-- Cycle fingerprint b097eb62f69455073f6cfeef59d820d3599ee516486c024c501b0e4a25aa3b50.
def localCycle00147 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![-2, 0, -1, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint b1955eba2201fed4cbcb743a62d5d7b83a3cca75d27e00fc9c46bdb0332150d7.
def localCycle00148 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 10 0, .triangle 11 0, .triangle 21 2, .triangle 24 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint b3a28aa9d9c7decffb8b533b6dbb2eecb602bea5ba542acbd44d245deff5ed4a.
def localCycle00149 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 33 1, .triangle 10 0, .triangle 9 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint b3b15603e3b123a9384385bf80f6e0c33eeadfe94bd031686fdd3165ecc7f576.
def localCycle00150 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .corridorLower 4 6]

-- Cycle fingerprint b443c0662d1beb83624b75d3625192a9f6c5171a2c247c0f94fdf9eb24db7bb3.
def localCycle00151 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .triangle 19 0, .gapLower 3 0]

-- Cycle fingerprint b48b630d2c4275f32dd166a29588824a614ccc2f16cb6c59e73436268b3d767f.
def localCycle00152 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .zero, .theta 6, .distance 1 6]
    constant := ![-2, -2, -1, 0, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .corridorLower 1 4, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint b494585c15fa3b0c9a6e18a300ae83fad2370415d325401b354b5ff4c793c017.
def localCycle00153 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint b66e8267c5d42b4520c2afad4c655f17ca8516755b280d07ef0ac16a71740a3b.
def localCycle00154 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 2, .triangle 23 1, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint b6d3c6c1c614ab15d80c4d746bf7fcf722fd47e5156f664493c00ffb2f3d377e.
def localCycle00155 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -1, -1, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 10 1, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint b77d638ff470197656691ee7eec845cb8271f1248171d5cbbf0e491a20f4c3df.
def localCycle00156 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint b792d5ca2eed732aebb814b4fb7df972fb175d1475f182214da73d1f001d0c8b.
def localCycle00157 : Cycle where
  length := 11
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 6]
    constant := ![3, 0, 0, -1, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 20 2, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint b884a9d13bfb675e90c92b8f441fb14aa6be033e01b8990910bde7c0181565ed.
def localCycle00158 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .gapLower 3 3, .triangle 10 0, .triangle 20 0, .gapLower 3 0]

-- Cycle fingerprint ba451e12164ed196eb98ba9d7118db99a953433b4a2049803408185901db2ee8.
def localCycle00159 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 10 1, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint bbc9e78ee0cc2fdc6f01fcd38789de074035d98df93895ab865ca6d41af72581.
def localCycle00160 : Cycle where
  length := 10
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6]
    constant := ![0, 0, -1, -1, -1, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint bc234728a725254b1322beb2d07e291625ea099a7e1da4d75a9300930c9c3ddf.
def localCycle00161 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint bf8ba95b741f263b7ab7b0268942cc02df81a4ade17ad62d7dcd4f42b9879452.
def localCycle00162 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 2, .triangle 11 1, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint c129afa894f152f5fe9f6489f93b378065f5e376e170eabbd5d12431ae578688.
def localCycle00163 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 10 0, .triangle 9 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint c2208c6c1612e34e22db4083e9ab17b8ac1fdd60a83c124473f86d49da078cb6.
def localCycle00164 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3]
    constant := ![-1, 0, -1, 0, -2, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 10 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0]

-- Cycle fingerprint c272a80e1b16523c00af29a0e8507d91029799b32dca215e53462a3baed74207.
def localCycle00165 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 10 1, .triangle 11 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint c275d7f40b035cf7241eab58aa0c1a0eb8cf60cc823c1a4e5265f7b16a7d0574.
def localCycle00166 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6]
    constant := ![-2, 0, -2, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint c37edbc58a114bb5636b7e04256f22624b7835b88a8b0edfcb4a6fb601574cc4.
def localCycle00167 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -1, 0, -1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint c3fa3266719f43e263b7de315dc4f416a99ae669ceb0542dbd01c8d611377196.
def localCycle00168 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![-1, 3, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 3, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint c53af95c34d186eddec354bae6d714a00b0677fbfb1f026e67ce425dec965d3b.
def localCycle00169 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![0, -1, -1, 0, -1, 0, -3, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint c5b93be061c8b8ddd6fc4bd669b7c964e90ae4851d11f15e103b3e15772a6855.
def localCycle00170 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 7 2, .triangle 10 1, .triangle 9 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint c62a74f8111a44ab213b58d017abbad7d88f2eec4155cf42762fdc44c590241f.
def localCycle00171 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint c78410087596996cd87cc117afa529659e6c4b79b99133f2de2790982d7a774d.
def localCycle00172 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 2, .triangle 11 1, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint c874ae4d24e34a885dc35b38b589adb49886574c2dc070a39316da2b4b43ebde.
def localCycle00173 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 10 1, .triangle 11 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint ca12eaa742d2be6316b242442def635f3b1d5e520d2bb009976600502bc8f9bf.
def localCycle00174 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 20 0, .gapLower 3 0]

-- Cycle fingerprint cb4af16716290a28f1122cb0e67c7a75750135dcad5de9319b19f10063fb175e.
def localCycle00175 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![0, 0, 3, 0, 0, -1, -1, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 20 2, .gapLower 1 3, .corridorLower 1 4]

-- Cycle fingerprint cb7d96d8d542ea330942e95261ee34b4b81e48cf34f4cb00aee51615bb4ed7e7.
def localCycle00176 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 9 0, .triangle 10 0, .triangle 20 0, .gapLower 3 0]

-- Cycle fingerprint cbbb79f6cbce34a8db8a0df369c8f3d99dea7864e969aa2a333604afbf538324.
def localCycle00177 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![0, -1, -1, 0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 20 2, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint cc99576c139647ffffeb4aee17b9a6a9cd6f5f57b988c31c0dbd3d6ea14a0fff.
def localCycle00178 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint ccc783c07867820664ae1280dc4a3c737d2b23335f832e305cd9b27131fe7de6.
def localCycle00179 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6]
    constant := ![-1, -1, 0, 0, 3, -1, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 0, .triangle 22 0, .gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 33 0]

-- Cycle fingerprint ce380dc113a5af665880881a12202aa0980ec80ea1f625a7d0c51f8dbdb0a680.
def localCycle00180 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .triangle 19 0, .gapLower 3 0]

-- Cycle fingerprint cefa3d9a7c47c2fc4d05e7700bd7d50fc5fe649c095ceeb2d1685c37c47c3c26.
def localCycle00181 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 5]
    constant := ![0, -1, -2, -1, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 31 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 4 2, .triangle 11 1, .triangle 10 0]

-- Cycle fingerprint cf4356824ffab03de7c286034d9a7c7e89a0d36de48e373e4c785bed6718b34e.
def localCycle00182 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 10 1, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint cfe59859940d7804a0c118fcc394d1e7b5cefc571e405e0111e59bc55164fbfc.
def localCycle00183 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 2, .gapLower 1 4, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint d05bed46e17fdafaf67c4435772b12e564e0bddde6e0594e0d0ded965532ae83.
def localCycle00184 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 6, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![-1, -1, 0, 0, -2, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 11 0, .triangle 9 0, .triangle 19 2, .triangle 22 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint d0c02935cee65de9c965c1001c0a9bf527348f1810265316d7a9cea226ca00a5.
def localCycle00185 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-1, 3, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 4, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint d14eb4a65bca3bb40a170776684ca07e4e56867ddcd54a98f236973a5f060808.
def localCycle00186 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 4, .distance 1 5]
    constant := ![-1, 0, 0, 2, -2, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 5, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint d25e60b43d3b4e77ad31676a9e4aad6e12d7c4c3e2040407a8f3e7da648b1f8b.
def localCycle00187 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 10 1, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint d52375e68db788f593c4f8422a3568640bb18f5e2d03a9312de2e869c0065ac6.
def localCycle00188 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint d81c6c0bd820a6330cb0aedc0a6029c7de609dc1aa65b4d0a7918e7b38776bcd.
def localCycle00189 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 3, 0, -1, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 19 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint d9e569c0110a6987ee6917a5e15caa37a7b011aa2373f6d8dc358d6453561bbd.
def localCycle00190 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3]
    constant := ![-1, 0, -1, 0, -1, -1, 0, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 27 0, .triangle 33 1, .triangle 14 0, .gapLower 0 3, .triangle 9 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0]

-- Cycle fingerprint da0282a53585b453b67637c1de39e93fc6875ad525dbe5913946b67bac415863.
def localCycle00191 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint dd6f610a7368b906b5020af90b8dab7675a89bc5ab7dc0f4a5fca068e8f67fde.
def localCycle00192 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 27 0, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 19 0, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint de201010f338cb393d9a66f41229d376f3532ebbc8404451b371375e978a2eaf.
def localCycle00193 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 2, .gapLower 1 4, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint deb3c7a13a56a3ebdcb84f529957d22434c82de452d147efefe35ba8b528a7a6.
def localCycle00194 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 20 2, .triangle 24 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint e1c65387e8fc7c654c30588675527d290e70eec3e9e792672a0139ae7aae7798.
def localCycle00195 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4]
    constant := ![-1, 0, -2, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0]

-- Cycle fingerprint e2b66063a93cbc068573e823cc51ba036775f31582bed56cdbe31049ed87d019.
def localCycle00196 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![4, 0, -1, -1, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint e38a749015b3df1a3c2ad0df62a188aa468b27c6e804f686f1537745b2dd376c.
def localCycle00197 : Cycle where
  length := 12
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3]
    constant := ![0, -1, 0, 0, 3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 10 0, .triangle 9 0, .triangle 19 0]

-- Cycle fingerprint e3c9d8521b4bdf48fc4f334c76c2b0828b8dfbabdd4f4082394e20df626401d7.
def localCycle00198 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint e7ca81d31fdb9b7449effe18fe1f9338a09e97947b15e4b9f8e440898af5cb21.
def localCycle00199 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6]
    constant := ![-2, -2, -1, 4, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 2]

-- Cycle fingerprint e83cfddab0ec1be74cf75d48fefdde28a20889286c9ec3d23eb56d9ac7083529.
def localCycle00200 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint ed340085c6c1399060f1d6f030cb7483e64b8a680193ad73268b82e9a9633aaa.
def localCycle00201 : Cycle where
  length := 10
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 3, .distance 3 4]
    constant := ![-1, 0, -1, 0, 0, 3, -1, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 11 0, .triangle 9 0]

-- Cycle fingerprint eeb5237be9f544972f1719ec7e8a092d841f17220708d8ef39bb9fb30538f4c7.
def localCycle00202 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, -1, -1, 0, -1, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint f0586507bdca001de57725c71b6c579032072e7c8bff05533666e1be15920eb2.
def localCycle00203 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 10 1, .triangle 11 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint f40068904cadff5c258d8da65c3a432502c4880f56ee53bb220c044ba0a14b53.
def localCycle00204 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 1 6, .distance 1 4, .theta 1]
    constant := ![0, 0, 2, -3, -1]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .corridorLower 1 4]

-- Cycle fingerprint f55dde6233a9bbe4b063e56852ea082281522e9be247f616c047dcbb510d1e3c.
def localCycle00205 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint f76a2f57595d8bc3c0d2bc25d1a848deed7bed7b0307545e3f1f70f99373ccb3.
def localCycle00206 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 2, .triangle 11 1, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint f8924e79e6a1a106c2420ce729b85dab705d54fb32d14d740ddd918572f67b92.
def localCycle00207 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6]
    constant := ![-1, 0, -2, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 21 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0]

-- Cycle fingerprint f93b1a7ae2f9a1c589f7ef2b33c6ff8ad91fe5b840c878b0f451d8ec791ee3d8.
def localCycle00208 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 10 0, .triangle 11 0, .triangle 21 0, .gapLower 3 0]

-- Cycle fingerprint fd3ba523112913f3a2c25a755f61b80b1e557224fc91d84f7ee00a3dec6ce484.
def localCycle00209 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 6, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 6, .corridorUpper 0 1]

-- Cycle fingerprint fe168f48d48af381052638b248b8be63bcf7b607be1b265a7edafc808bfd6f1b.
def localCycle00210 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 1]

def library : Library := fun id => if id < 105 then (if id < 52 then (if id < 26 then (if id < 13 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none))))) else (if id < 19 then (if id < 16 then (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none))) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)))) else (if id < 22 then (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none))) else (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)))))) else (if id < 39 then (if id < 32 then (if id < 29 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none))) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)))) else (if id < 35 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none))) else (if id < 37 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none)) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))))) else (if id < 45 then (if id < 42 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none)))) else (if id < 48 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none))) else (if id < 50 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))))))) else (if id < 78 then (if id < 65 then (if id < 58 then (if id < 55 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none))) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)))) else (if id < 61 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))) else (if id < 63 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none))))) else (if id < 71 then (if id < 68 then (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none))) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)))) else (if id < 74 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none))) else (if id < 76 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)))))) else (if id < 91 then (if id < 84 then (if id < 81 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none))) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)))) else (if id < 87 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none))) else (if id < 89 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none))))) else (if id < 98 then (if id < 94 then (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none))) else (if id < 96 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)))) else (if id < 101 then (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))) else (if id < 103 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)))))))) else (if id < 158 then (if id < 131 then (if id < 118 then (if id < 111 then (if id < 108 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none))) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)))) else (if id < 114 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none))) else (if id < 116 then (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none)) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none))))) else (if id < 124 then (if id < 121 then (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none))) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)))) else (if id < 127 then (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none))) else (if id < 129 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)))))) else (if id < 144 then (if id < 137 then (if id < 134 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none))) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)))) else (if id < 140 then (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none))) else (if id < 142 then (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none)) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none))))) else (if id < 151 then (if id < 147 then (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none))) else (if id < 149 then (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none)) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)))) else (if id < 154 then (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none))) else (if id < 156 then (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none)) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none))))))) else (if id < 184 then (if id < 171 then (if id < 164 then (if id < 161 then (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none))) else (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none)))) else (if id < 167 then (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none))) else (if id < 169 then (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none)) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none))))) else (if id < 177 then (if id < 174 then (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id = 173 then some localCycle00173 else none))) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none)))) else (if id < 180 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none))) else (if id < 182 then (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none)) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id = 183 then some localCycle00183 else none)))))) else (if id < 197 then (if id < 190 then (if id < 187 then (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none))) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none)))) else (if id < 193 then (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none))) else (if id < 195 then (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none)) else (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none))))) else (if id < 204 then (if id < 200 then (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none))) else (if id < 202 then (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none)) else (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id = 203 then some localCycle00203 else none)))) else (if id < 207 then (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id = 206 then some localCycle00206 else none))) else (if id < 209 then (if id < 208 then (if id = 207 then some localCycle00207 else none) else (if id = 208 then some localCycle00208 else none)) else (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id = 210 then some localCycle00210 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 6, 3, 5, 4, 0], ![1, 0, 6, 5, 4, 3], ![6, 1, 0, 5, 4, 2], ![6, 5, 1, 0, 3, 2], ![6, 4, 1, 0, 3, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 156 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18176)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 4, 3, 6], ![1, 5, 0, 4, 2, 6], ![1, 5, 0, 3, 2, 6], ![1, 4, 3, 0, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 28 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18177)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 4, 6, 3], ![1, 5, 0, 4, 6, 2], ![1, 5, 0, 3, 2, 6], ![1, 4, 3, 0, 2, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 176 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18178)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 5, 0, 4, 6, 2], ![1, 5, 0, 3, 6, 2], ![1, 4, 3, 0, 2, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 158 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18179)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 5, 0, 6, 4, 2], ![1, 5, 0, 6, 3, 2], ![1, 4, 3, 0, 2, 6], ![1, 0, 4, 3, 2, 5]], proof := .tail 61 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18180)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 0, 4, 6, 2], ![1, 5, 0, 3, 6, 2], ![1, 4, 3, 0, 6, 2], ![1, 0, 3, 4, 5, 2]], proof := .tail 89 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18181)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 0, 6, 4, 2], ![1, 5, 0, 6, 3, 2], ![1, 4, 3, 0, 6, 2], ![1, 0, 4, 3, 5, 2]], proof := .tail 61 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18182)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![2, 5, 3, 6, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 5, 0, 6, 4, 2], ![1, 5, 6, 0, 3, 2], ![1, 4, 3, 0, 2, 6], ![1, 4, 0, 3, 2, 5]], proof := .tail 174 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18183)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![2, 5, 3, 6, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 0, 6, 4, 2], ![1, 5, 6, 0, 3, 2], ![1, 4, 3, 0, 6, 2], ![1, 4, 0, 3, 5, 2]], proof := .tail 10 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18184)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 5, 6, 0, 4, 2], ![1, 5, 6, 0, 3, 2], ![1, 4, 3, 0, 2, 6], ![1, 4, 3, 0, 2, 5]], proof := .tail 41 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18185)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 6, 0, 4, 2], ![1, 5, 6, 0, 3, 2], ![1, 4, 3, 0, 6, 2], ![1, 4, 3, 0, 5, 2]], proof := .tail 41 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18186)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 6, 0, 4, 2], ![1, 5, 6, 0, 3, 2], ![1, 4, 3, 6, 0, 2], ![1, 4, 3, 5, 0, 2]], proof := .tail 15 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18187)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 5, 0, 4, 2], ![1, 5, 6, 0, 3, 2], ![1, 4, 6, 3, 0, 2], ![1, 4, 5, 3, 0, 2]], proof := .tail 179 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18188)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 5, 0, 4, 2], ![1, 6, 5, 0, 3, 2], ![1, 6, 4, 3, 0, 2], ![1, 5, 4, 3, 0, 2]], proof := .tail 138 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18189)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 5, 0, 4, 2], ![1, 6, 5, 0, 3, 2], ![6, 1, 4, 3, 0, 2], ![5, 1, 4, 3, 0, 2]], proof := .tail 194 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18190)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 5, 0, 4, 2], ![6, 1, 5, 0, 3, 2], ![6, 1, 4, 3, 0, 2], ![5, 4, 1, 3, 0, 2]], proof := .tail 20 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18191)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 6, 3, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![6, 1, 5, 0, 4, 2], ![6, 1, 5, 0, 3, 2], ![6, 1, 4, 3, 0, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 50 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18192)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 4, 3, 6], ![1, 5, 0, 4, 2, 6], ![5, 1, 0, 3, 2, 6], ![4, 1, 3, 0, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 28 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18193)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 4, 6, 3], ![1, 5, 0, 4, 6, 2], ![5, 1, 0, 3, 2, 6], ![4, 1, 3, 0, 2, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 176 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18194)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 5, 0, 4, 6, 2], ![5, 1, 0, 3, 6, 2], ![4, 1, 3, 0, 2, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 158 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18195)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 5, 0, 6, 4, 2], ![5, 1, 0, 6, 3, 2], ![4, 1, 3, 0, 2, 6], ![1, 0, 4, 3, 2, 5]], proof := .tail 61 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18196)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![2, 5, 3, 6, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 5, 0, 6, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 1, 3, 0, 2, 6], ![1, 4, 0, 3, 2, 5]], proof := .tail 17 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18197)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![2, 5, 3, 6, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 5, 6, 4, 3], ![1, 5, 0, 6, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 1, 3, 0, 2, 6], ![4, 1, 0, 3, 2, 5]], proof := .tail 174 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18198)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 0, 4, 6, 2], ![5, 1, 0, 3, 6, 2], ![4, 1, 3, 0, 6, 2], ![1, 0, 3, 4, 5, 2]], proof := .tail 89 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18199)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 0, 6, 4, 2], ![5, 1, 0, 6, 3, 2], ![4, 1, 3, 0, 6, 2], ![1, 0, 4, 3, 5, 2]], proof := .tail 61 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18200)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![2, 5, 3, 6, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 0, 6, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 1, 3, 0, 6, 2], ![1, 4, 0, 3, 5, 2]], proof := .tail 17 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18201)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![2, 5, 3, 6, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 0, 6, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 1, 3, 0, 6, 2], ![4, 1, 0, 3, 5, 2]], proof := .tail 10 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18202)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 5, 6, 0, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 1, 3, 0, 2, 6], ![1, 4, 3, 0, 2, 5]], proof := .tail 107 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18203)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 6, 0, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 1, 3, 0, 6, 2], ![1, 4, 3, 0, 5, 2]], proof := .tail 107 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18204)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 6, 0, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 1, 3, 6, 0, 2], ![1, 4, 3, 5, 0, 2]], proof := .tail 15 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18205)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 5, 0, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 1, 6, 3, 0, 2], ![1, 4, 5, 3, 0, 2]], proof := .tail 99 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18206)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 5, 6, 4, 3], ![1, 5, 6, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 1, 3, 0, 2, 6], ![4, 1, 3, 0, 2, 5]], proof := .tail 41 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18207)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 6, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 1, 3, 0, 6, 2], ![4, 1, 3, 0, 5, 2]], proof := .tail 41 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18208)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 5, 6, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 1, 3, 6, 0, 2], ![4, 1, 3, 5, 0, 2]], proof := .tail 15 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18209)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 5, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 1, 6, 3, 0, 2], ![4, 1, 5, 3, 0, 2]], proof := .tail 99 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18210)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 5, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 6, 1, 3, 0, 2], ![4, 5, 1, 3, 0, 2]], proof := .tail 121 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18211)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 5, 0, 4, 2], ![6, 5, 1, 0, 3, 2], ![6, 4, 1, 3, 0, 2], ![5, 4, 1, 3, 0, 2]], proof := .tail 109 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18212)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 6, 3, 5, 4, 0], ![1, 0, 6, 5, 4, 3], ![6, 1, 5, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 6, 1, 3, 0, 2], ![4, 5, 3, 1, 0, 2]], proof := .tail 105 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18213)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 6, 3, 5, 4, 0], ![1, 0, 6, 5, 4, 3], ![6, 1, 5, 0, 4, 2], ![6, 5, 1, 0, 3, 2], ![6, 4, 1, 3, 0, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 50 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18214)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 5, 4, 3, 6], ![5, 1, 0, 4, 2, 6], ![5, 1, 0, 3, 2, 6], ![4, 3, 1, 0, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 63 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18215)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 5, 4, 6, 3], ![5, 1, 0, 4, 6, 2], ![5, 1, 0, 3, 2, 6], ![4, 3, 1, 0, 2, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 145 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18216)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 5, 6, 4, 3], ![5, 1, 0, 4, 6, 2], ![5, 1, 0, 3, 6, 2], ![4, 3, 1, 0, 2, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 14 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18217)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 5, 6, 4, 3], ![5, 1, 0, 6, 4, 2], ![5, 1, 0, 6, 3, 2], ![4, 3, 1, 0, 2, 6], ![1, 0, 4, 3, 2, 5]], proof := .tail 85 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18218)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![2, 5, 3, 6, 4, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 5, 6, 4, 3], ![5, 1, 0, 6, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 3, 1, 0, 2, 6], ![1, 4, 0, 3, 2, 5]], proof := .tail 85 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18219)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![2, 5, 3, 6, 4, 1], ![2, 5, 3, 6, 4, 0], ![1, 0, 5, 6, 4, 3], ![5, 1, 0, 6, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 3, 1, 0, 2, 6], ![4, 1, 0, 3, 2, 5]], proof := .tail 102 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18220)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![5, 1, 0, 4, 6, 2], ![5, 1, 0, 3, 6, 2], ![4, 3, 1, 0, 6, 2], ![1, 0, 3, 4, 5, 2]], proof := .tail 171 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18221)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![5, 1, 0, 6, 4, 2], ![5, 1, 0, 6, 3, 2], ![4, 3, 1, 0, 6, 2], ![1, 0, 4, 3, 5, 2]], proof := .tail 85 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18222)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![2, 5, 3, 6, 4, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![5, 1, 0, 6, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 3, 1, 0, 6, 2], ![1, 4, 0, 3, 5, 2]], proof := .tail 85 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18223)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![2, 5, 3, 6, 4, 1], ![2, 5, 3, 6, 4, 0], ![1, 0, 6, 5, 4, 3], ![5, 1, 0, 6, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 3, 1, 0, 6, 2], ![4, 1, 0, 3, 5, 2]], proof := .tail 119 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18224)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 5, 6, 4, 3], ![5, 1, 6, 0, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 3, 1, 0, 2, 6], ![1, 4, 3, 0, 2, 5]], proof := .tail 34 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18225)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![5, 1, 6, 0, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 3, 1, 0, 6, 2], ![1, 4, 3, 0, 5, 2]], proof := .tail 34 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18226)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![5, 1, 6, 0, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 3, 1, 6, 0, 2], ![1, 4, 3, 5, 0, 2]], proof := .tail 15 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18227)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 5, 3, 6, 4, 0], ![1, 0, 5, 6, 4, 3], ![5, 1, 6, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 3, 1, 0, 2, 6], ![4, 1, 3, 0, 2, 5]], proof := .tail 34 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18228)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 5, 3, 6, 4, 0], ![1, 0, 6, 5, 4, 3], ![5, 1, 6, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 3, 1, 0, 6, 2], ![4, 1, 3, 0, 5, 2]], proof := .tail 34 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18229)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 5, 3, 6, 4, 0], ![1, 0, 6, 5, 4, 3], ![5, 1, 6, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 3, 1, 6, 0, 2], ![4, 1, 3, 5, 0, 2]], proof := .tail 69 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18230)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 5, 6, 3, 4, 0], ![1, 0, 5, 6, 4, 3], ![5, 6, 1, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 3, 1, 0, 2, 6], ![4, 3, 1, 0, 2, 5]], proof := .tail 188 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18231)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 5, 6, 3, 4, 0], ![1, 0, 6, 5, 4, 3], ![5, 6, 1, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 3, 1, 0, 6, 2], ![4, 3, 1, 0, 5, 2]], proof := .tail 188 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18232)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 5, 6, 3, 4, 0], ![1, 0, 6, 5, 4, 3], ![5, 6, 1, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 3, 1, 6, 0, 2], ![4, 3, 1, 5, 0, 2]], proof := .tail 15 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18233)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 6, 5, 3, 4, 0], ![1, 0, 6, 5, 4, 3], ![5, 6, 1, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 3, 6, 1, 0, 2], ![4, 3, 5, 1, 0, 2]], proof := .tail 15 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18234)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 6, 5, 3, 4, 0], ![1, 0, 6, 5, 4, 3], ![6, 5, 1, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 6, 3, 1, 0, 2], ![4, 5, 3, 1, 0, 2]], proof := .tail 99 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18235)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 6, 5, 3, 4, 0], ![1, 0, 6, 5, 4, 3], ![6, 5, 1, 0, 4, 2], ![6, 5, 1, 0, 3, 2], ![6, 4, 3, 1, 0, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 198 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18236)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 3, 5, 6], ![1, 4, 0, 2, 5, 6], ![1, 3, 0, 2, 5, 6], ![1, 0, 2, 3, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 29 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18237)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 3, 5, 6], ![1, 4, 0, 2, 5, 6], ![1, 3, 0, 2, 6, 5], ![1, 0, 2, 3, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 33 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18238)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 3, 5, 6], ![1, 4, 0, 2, 6, 5], ![1, 3, 0, 2, 6, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 3, 4]], proof := .tail 170 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18239)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 3, 6, 5], ![1, 4, 0, 2, 6, 5], ![1, 3, 0, 2, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 3, 4]], proof := .tail 91 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18240)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![2, 4, 3, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 3, 6, 5], ![1, 4, 0, 2, 6, 5], ![1, 3, 0, 2, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 3, 4]], proof := .low (![87, 114, 129, 118, 65, 205, 187, 11, 23, 62, 30, 195, 155, 111, 196, 141, 161, 159, 131, 183, 147, 130, 199, 31, 182, 19, 182, 182]) }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18241)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![2, 4, 3, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 4, 3, 6, 5], ![1, 4, 0, 2, 6, 5], ![1, 3, 0, 2, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low (![87, 114, 27, 83, 93, 124, 187, 11, 59, 98, 43, 32, 155, 189, 51, 104, 161, 159, 168, 70, 68, 122, 185, 6, 182, 209, 153, 140]) }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18242)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 6, 3, 5], ![1, 4, 0, 6, 2, 5], ![1, 3, 0, 2, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 3, 2, 4]], proof := .tail 190 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18243)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![2, 4, 3, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 6, 3, 5], ![1, 4, 0, 6, 2, 5], ![1, 3, 0, 2, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 3, 2, 4]], proof := .tail 120 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18244)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![2, 4, 3, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 4, 6, 3, 5], ![1, 4, 0, 6, 2, 5], ![1, 3, 0, 2, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 3, 2, 4]], proof := .tail 120 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18245)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 3, 5], ![1, 4, 0, 6, 2, 5], ![1, 3, 0, 6, 2, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 3, 4, 2]], proof := .tail 48 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18246)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![2, 4, 3, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 3, 5], ![1, 4, 0, 6, 2, 5], ![1, 3, 0, 6, 2, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 3, 4, 2]], proof := .tail 53 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18247)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![2, 4, 3, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 3, 5], ![1, 4, 0, 6, 2, 5], ![1, 3, 0, 6, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 3, 4, 2]], proof := .tail 53 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18248)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![2, 4, 6, 3, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 6, 3, 5], ![1, 4, 6, 0, 2, 5], ![1, 3, 0, 2, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 3, 0, 2, 4]], proof := .low (![42, 3, 144, 0, 65, 205, 203, 46, 113, 202, 139, 207, 133, 82, 167, 193, 37, 173, 103, 16, 66, 132, 16, 136, 49, 19, 165, 165]) }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18249)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![2, 4, 6, 3, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 3, 5], ![1, 4, 6, 0, 2, 5], ![1, 3, 0, 6, 2, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 3, 0, 4, 2]], proof := .tail 48 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18250)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 3, 5], ![1, 4, 6, 0, 2, 5], ![1, 3, 6, 0, 2, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 3, 4, 0, 2]], proof := .tail 45 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18251)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 3, 5], ![1, 6, 4, 0, 2, 5], ![1, 6, 3, 0, 2, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 3, 0, 2]], proof := .tail 106 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18252)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![2, 4, 6, 3, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 4, 6, 3, 5], ![1, 4, 6, 0, 2, 5], ![1, 3, 0, 2, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 3, 0, 2, 4]], proof := .low (![42, 3, 27, 123, 93, 108, 203, 46, 154, 90, 43, 207, 133, 79, 73, 37, 37, 173, 100, 2, 68, 24, 143, 6, 165, 209, 153, 84]) }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18253)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![2, 4, 6, 3, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 3, 5], ![1, 4, 6, 0, 2, 5], ![1, 3, 0, 6, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 3, 0, 4, 2]], proof := .tail 48 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18254)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 3, 5], ![1, 4, 6, 0, 2, 5], ![1, 3, 6, 0, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 3, 4, 0, 2]], proof := .tail 45 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18255)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 3, 5], ![1, 6, 4, 0, 2, 5], ![1, 6, 3, 0, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 3, 0, 2]], proof := .tail 38 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18256)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 4, 3, 5], ![1, 6, 4, 0, 2, 5], ![6, 1, 3, 0, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 3, 0, 2]], proof := .tail 97 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18257)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 6, 3, 4, 5, 0], ![1, 0, 6, 4, 3, 5], ![6, 1, 4, 0, 2, 5], ![6, 1, 3, 0, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 8 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18258)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 5, 3, 6], ![1, 4, 0, 5, 2, 6], ![1, 3, 0, 2, 5, 6], ![1, 0, 3, 2, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 197 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18259)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 5, 3, 6], ![1, 4, 0, 5, 2, 6], ![1, 3, 0, 2, 6, 5], ![1, 0, 3, 2, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 26 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18260)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 5, 6, 3], ![1, 4, 0, 5, 6, 2], ![1, 3, 0, 2, 5, 6], ![1, 0, 3, 2, 4, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 149 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18261)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 5, 6, 3], ![1, 4, 0, 5, 6, 2], ![1, 3, 0, 2, 6, 5], ![1, 0, 3, 2, 6, 4], ![1, 0, 3, 2, 5, 4]], proof := .tail 125 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18262)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 6, 5, 3], ![1, 4, 0, 5, 6, 2], ![1, 3, 0, 2, 6, 5], ![1, 0, 3, 6, 2, 4], ![1, 0, 3, 5, 2, 4]], proof := .tail 151 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18263)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 6, 5, 3], ![1, 4, 0, 6, 5, 2], ![1, 3, 0, 2, 6, 5], ![1, 0, 6, 3, 2, 4], ![1, 0, 5, 3, 2, 4]], proof := .tail 180 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18264)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![2, 4, 3, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 6, 5, 3], ![1, 4, 0, 6, 5, 2], ![1, 3, 0, 2, 6, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 0, 3, 2, 4]], proof := .tail 201 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18265)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![2, 4, 3, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 4, 6, 5, 3], ![1, 4, 0, 6, 5, 2], ![1, 3, 0, 2, 6, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 0, 3, 2, 4]], proof := .tail 201 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18266)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 4, 0, 5, 6, 2], ![1, 3, 0, 6, 2, 5], ![1, 0, 3, 6, 2, 4], ![1, 0, 3, 5, 4, 2]], proof := .tail 40 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18267)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 4, 0, 6, 5, 2], ![1, 3, 0, 6, 2, 5], ![1, 0, 6, 3, 2, 4], ![1, 0, 5, 3, 4, 2]], proof := .tail 81 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18268)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![2, 4, 3, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 4, 0, 6, 5, 2], ![1, 3, 0, 6, 2, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 0, 3, 4, 2]], proof := .tail 53 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18269)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![2, 4, 3, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 5, 3], ![1, 4, 0, 6, 5, 2], ![1, 3, 0, 6, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 0, 3, 4, 2]], proof := .tail 53 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18270)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![2, 4, 6, 3, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 6, 5, 3], ![1, 4, 6, 0, 5, 2], ![1, 3, 0, 2, 6, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 3, 0, 2, 4]], proof := .tail 208 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18271)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![2, 4, 6, 3, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 4, 6, 0, 5, 2], ![1, 3, 0, 6, 2, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 3, 0, 4, 2]], proof := .tail 48 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18272)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 4, 6, 0, 5, 2], ![1, 3, 6, 0, 2, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 3, 4, 0, 2]], proof := .tail 44 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18273)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 6, 4, 0, 5, 2], ![1, 6, 3, 0, 2, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 4, 3, 0, 2]], proof := .tail 135 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18274)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![2, 4, 6, 3, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 4, 6, 5, 3], ![1, 4, 6, 0, 5, 2], ![1, 3, 0, 2, 6, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 3, 0, 2, 4]], proof := .tail 208 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18275)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![2, 4, 6, 3, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 5, 3], ![1, 4, 6, 0, 5, 2], ![1, 3, 0, 6, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 3, 0, 4, 2]], proof := .tail 148 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18276)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 5, 3], ![1, 4, 6, 0, 5, 2], ![1, 3, 6, 0, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 3, 4, 0, 2]], proof := .tail 44 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18277)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 5, 3], ![1, 6, 4, 0, 5, 2], ![1, 6, 3, 0, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 4, 3, 0, 2]], proof := .tail 94 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18278)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 4, 5, 3], ![1, 6, 4, 0, 5, 2], ![6, 1, 3, 0, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 4, 1, 3, 0, 2]], proof := .tail 35 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18279)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 6, 3, 4, 5, 0], ![1, 0, 6, 4, 5, 3], ![6, 1, 4, 0, 5, 2], ![6, 1, 3, 0, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 163 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18280)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 4, 3, 6], ![1, 4, 0, 5, 2, 6], ![1, 3, 0, 5, 2, 6], ![1, 0, 3, 4, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 146 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18281)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 4, 6, 3], ![1, 4, 0, 5, 6, 2], ![1, 3, 0, 5, 2, 6], ![1, 0, 3, 4, 2, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 146 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18282)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 4, 0, 5, 6, 2], ![1, 3, 0, 5, 6, 2], ![1, 0, 3, 4, 2, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 110 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18283)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 0, 5, 6, 2], ![1, 3, 0, 5, 6, 2], ![1, 0, 3, 4, 6, 2], ![1, 0, 3, 4, 5, 2]], proof := .tail 58 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18284)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 0, 5, 6, 2], ![1, 3, 0, 6, 5, 2], ![1, 0, 3, 6, 4, 2], ![1, 0, 3, 5, 4, 2]], proof := .tail 5 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18285)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 0, 6, 5, 2], ![1, 3, 0, 6, 5, 2], ![1, 0, 6, 3, 4, 2], ![1, 0, 5, 3, 4, 2]], proof := .tail 36 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18286)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![2, 4, 3, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 0, 6, 5, 2], ![1, 3, 0, 6, 5, 2], ![1, 6, 0, 3, 4, 2], ![1, 5, 0, 3, 4, 2]], proof := .tail 126 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18287)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![2, 4, 3, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 0, 6, 5, 2], ![1, 3, 0, 6, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 1, 0, 3, 4, 2]], proof := .tail 126 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18288)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![2, 4, 6, 3, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 6, 0, 5, 2], ![1, 3, 0, 6, 5, 2], ![1, 6, 0, 3, 4, 2], ![1, 5, 3, 0, 4, 2]], proof := .tail 12 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18289)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![2, 4, 6, 3, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 6, 0, 5, 2], ![1, 3, 0, 6, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 1, 3, 0, 4, 2]], proof := .tail 12 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18290)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 6, 0, 5, 2], ![1, 3, 6, 0, 5, 2], ![1, 6, 0, 3, 4, 2], ![1, 5, 3, 4, 0, 2]], proof := .tail 200 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18291)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 4, 0, 5, 2], ![1, 6, 3, 0, 5, 2], ![1, 6, 0, 3, 4, 2], ![1, 5, 4, 3, 0, 2]], proof := .tail 25 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18292)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 4, 6, 0, 5, 2], ![1, 3, 6, 0, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 1, 3, 4, 0, 2]], proof := .tail 200 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18293)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 4, 0, 5, 2], ![1, 6, 3, 0, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 1, 4, 3, 0, 2]], proof := .tail 150 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18294)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 4, 0, 5, 2], ![6, 1, 3, 0, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 4, 1, 3, 0, 2]], proof := .tail 88 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18295)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 6, 3, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![6, 1, 4, 0, 5, 2], ![6, 1, 3, 0, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 134 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18296)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 5, 3, 6], ![1, 4, 5, 0, 2, 6], ![1, 3, 0, 2, 5, 6], ![1, 3, 0, 2, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .low (![169, 1, 27, 175, 39, 205, 76, 127, 115, 157, 95, 164, 86, 128, 177, 71, 52, 181, 75, 64, 178, 142, 152, 74, 92, 19, 80, 55]) }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18297)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 5, 3, 6], ![1, 4, 5, 0, 2, 6], ![1, 3, 0, 2, 6, 5], ![1, 3, 0, 2, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 192 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18298)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 4, 3, 6], ![1, 4, 5, 0, 2, 6], ![1, 3, 0, 5, 2, 6], ![1, 3, 0, 4, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 191 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18299)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 4, 3, 6], ![1, 4, 5, 0, 2, 6], ![1, 3, 5, 0, 2, 6], ![1, 3, 4, 0, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 22 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18300)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 4, 3, 6], ![1, 5, 4, 0, 2, 6], ![1, 5, 3, 0, 2, 6], ![1, 4, 3, 0, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 77 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18301)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 4, 3, 6], ![1, 5, 4, 0, 2, 6], ![5, 1, 3, 0, 2, 6], ![4, 1, 3, 0, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .low (![4, 9, 18, 47, 204, 13, 172, 57, 60, 56, 116, 160, 101, 184, 72, 166, 67, 206, 112, 117, 210, 96, 186, 21, 78, 7, 162, 137]) }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18302)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 5, 6, 3], ![1, 4, 5, 0, 6, 2], ![1, 3, 0, 2, 5, 6], ![1, 3, 0, 2, 4, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 54 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18303)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (18176 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 18176 ≤ id.val) (hhigh : id.val < 18304) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 18176)) = true := by
  let j : Fin 128 := ⟨id.val - 18176, by omega⟩
  have hsum : 18176 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (18176 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard142
