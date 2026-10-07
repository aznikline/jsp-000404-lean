import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard124
open N4R2RowDataReplay

-- Original cycle 0014ed250aeaefe308a4834966c56208df3fca5fd14b1890d7f84e16e21a860c; original global index 10.
def localCycle00000 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 0 6, .distance 0 3]
    constant := ![2, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 30 1, .gapLower 6 3, .triangle 11 1]

-- Original cycle 0098a678ef459ca4ef0a25dc019d4fda408b458100b0a086f4ce91b81122a4fb; original global index 53.
def localCycle00001 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 21 2, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 00e649d1deb690b335d9138897133bcde133b94d7b06b59269222194bf6b0070; original global index 78.
def localCycle00002 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 15 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 01148c2dd385c3f214930bf2fa2ebefe7120ba26d9f62599cca71ce9bcdbe0da; original global index 95.
def localCycle00003 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 0, .triangle 20 1, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 017cd4f53c1a3fab84647abebec28672a8c25ce4f790bf3e587d34a2434773d6; original global index 124.
def localCycle00004 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 03380c4c311898c8a6b779fcbe89fde34e263fae08f734ee2a086b566861af63; original global index 259.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 27 2, .triangle 30 1, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 03967526b63aa0a81af6c4a4267b9f3d7be96c91ccbd03b8a12b267737f60e82; original global index 292.
def localCycle00006 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 0, .triangle 17 1, .triangle 15 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 04a5b7e27c20478c6766b463c98081500a7a267014e04f0c7932ff6dd33b239f; original global index 369.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 2, .triangle 24 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 04b58ee6ffa969a76a529329873c490f118c1303492ba7a0aca710bc75c02f86; original global index 376.
def localCycle00008 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 0, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 04f8b2ef7aeda52659761a3e3ef3f4f26e6668c67c4b8374589259f90935c0ab; original global index 397.
def localCycle00009 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 1]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 1 3, .gapLower 6 3, .triangle 4 1]

-- Original cycle 0711b0a092620f5a6b3880e22ea399016adf982d5bbe9b564dced76ac0797d15; original global index 581.
def localCycle00010 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![4, 0, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 0, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 0894ddb6e6b45e0e74436ddc3502470f538ff402aae2b2a228b84af1fca4b302; original global index 681.
def localCycle00011 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 2 0, .triangle 0 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 092542769fa3337a1b5e754c18bc0a0a23a722443ae5e96dc5892bafb65d1945; original global index 730.
def localCycle00012 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 092e7a3461a55e47cfe3ba518977943b58a6c3846e7d95095ba95138d0d6514e; original global index 735.
def localCycle00013 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 0987783e1cb06325e50829b56f14856c2a0674bd925f1b0f7040c147b35a2ba0; original global index 759.
def localCycle00014 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 2 0, .triangle 3 0, .triangle 22 1, .corridorLower 4 5]

-- Original cycle 09aa8c751b0bb7a7625793ec7e3bb2df5a8593c3760b01af1625b1790faa0a3f; original global index 771.
def localCycle00015 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 3]
    constant := ![2, -3, 0, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 8 2, .triangle 11 1]

-- Original cycle 0cb0ddbe022a8fd82866bf1937b76a7377e86afdc82be627fc6c489fb72b0d94; original global index 1005.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 3 2, .triangle 14 2, .gapLower 6 2, .triangle 34 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 0e1e0eaec3f7acf7f272596ab2f1e6c0abc281c3bd6e0f9e780acf4efa65db1a; original global index 1114.
def localCycle00017 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 0, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 0e67ce7677b90986c921925935af700179be59e1276337a0e671b8b242ac0548; original global index 1139.
def localCycle00018 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 2, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 0f4ee20ac505d2f245153c2f31a650290903a7e5d1a6f3b640378aa06c36d2c8; original global index 1217.
def localCycle00019 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 0f7e0f45387fe80168b7b430c4bd7f6e892f190e34a1518dd243d2e319640bd8; original global index 1231.
def localCycle00020 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 0, .triangle 23 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 1210373bebb66e41c06695f34397571f0bdc5512fe1e8f8a06eea6da67dee864; original global index 1442.
def localCycle00021 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 0 4]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 12 2, .triangle 14 0, .gapLower 6 1, .gapUpper 4 2]

-- Original cycle 1353ebd34009a15b6fa8b857a260fd60112974d93e3ba4c1b4b04499a71e8d13; original global index 1523.
def localCycle00022 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 13 0, .triangle 2 1, .triangle 3 0, .triangle 22 1, .corridorLower 4 5]

-- Original cycle 14ffec48bcf7749a94e505c416901be886eb519ca1faa02b31d8a3cf95a5a0d1; original global index 1665.
def localCycle00023 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 4 6, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 1, .gapLower 6 1, .triangle 34 1]

-- Original cycle 156dd284e57279f12f26880c9b9bee496e1aca4f50895ea7474ff47a34dd5d9f; original global index 1698.
def localCycle00024 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 17 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 15ecdda9ea9a91e388d572012dbdf5a059f2b28c9666c481fe7285b9b89f1366; original global index 1739.
def localCycle00025 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 1874005b9ab5c9f133ed6b58d2b6a89535d4d4741074b564da795405dbdd67da; original global index 1915.
def localCycle00026 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 3, .gapLower 6 3, .triangle 14 1]

-- Original cycle 1ce2761d144224d7012cc9fcd1eb46e5423f8e1631c978369560c9bb82a51830; original global index 2224.
def localCycle00027 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 1ce3615da3f905f77dba703d510da1cf1269fde0e799787bc983466648162821; original global index 2226.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 0, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 21ab2c8c27f3fc3f5fcfb333511d3f99dd782b33f677ef8f29d5b703362d5cc9; original global index 2577.
def localCycle00029 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 2, .gapLower 6 3, .triangle 23 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 220159b062ddbf5d8c8a6e5688507faa4488e1194a49d3a318d424d14626d59e; original global index 2602.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, 0, -3, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 32 2, .gapLower 6 4, .triangle 18 2, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 15 0, .gapLower 3 0]

-- Original cycle 22fda38e0238708bd673c17927a0e54e5103cade2a4a4fac2bb18fc00a0d1e99; original global index 2685.
def localCycle00031 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 12 2, .triangle 14 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 25590e87a2a19886aeca6ac70222bef12c72ce104c0a0145c4e1d21dbc61bb3d; original global index 2872.
def localCycle00032 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 15 2, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 2710990c3e290d5d6c6b1de5b33474455ed9b160e6a63b64e9381cc00eaad137; original global index 2994.
def localCycle00033 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 17 2, .triangle 3 0, .triangle 0 0, .triangle 15 0, .gapLower 3 0]

-- Original cycle 282fa741fd0eae3ea09a38e89798ca5301590039dc8c6ee0e3ae258c14ec1998; original global index 3074.
def localCycle00034 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 2, .triangle 8 0, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 28d01a9e8e4a48a486565d2826e12d0891a64f2f0d59c2e39d106694121db6b7; original global index 3125.
def localCycle00035 : Cycle where
  length := 19
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 5 6, .theta 6, .theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -2, 0, 3, 0, 0, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, true, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 12 0, .triangle 34 0, .gapLower 6 0, .thetaNext 5, .corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .triangle 4 1, .triangle 0 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 2a5e02c26e3e4bb66b97efd944f6c7cec38383ba6953d3ba462e2af7a0f9e841; original global index 3230.
def localCycle00036 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 13 2, .gapLower 6 1, .gapUpper 4 2]

-- Original cycle 2ae18e3177a1923c34129f9b16df25fff003891b2c245276c57fb6c93a0a2f55; original global index 3271.
def localCycle00037 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![4, 0, 0, -1, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 2e0e5344ebf2cee64765c1874c1151634a05694c0084f165bd50aaa9126747ca; original global index 3519.
def localCycle00038 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 2e1633e05f967cf8258391e23e392c21fc13c754d9ac54d9441adfe17d340c05; original global index 3521.
def localCycle00039 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 2e25a51613dcd9c39401b807d14bea5793952aedd03fbb7212199a51abdd1756; original global index 3525.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .gapLower 4 0]

-- Original cycle 2f820611cdecb6a89717a06a7ca09d1552e21cbf29d4d2bf473fb05455374a5e; original global index 3629.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 29 1, .corridorLower 4 6]

-- Original cycle 304301f493f3674b72c3e2162df5835a0ce78393af680d3f1cf34a7ede376603; original global index 3674.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 308a8c053c3fe8123dd3512c396c447ab4954703ba78e4528cd68206c7996c5b; original global index 3697.
def localCycle00043 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 3096b8de50bbbdcb009591beb2de1237e78ba0feb00baf6b9d35aeb4bc96f347; original global index 3705.
def localCycle00044 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 2, .gapLower 6 2, .triangle 23 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 311505cd80e9be0f5dfa6210fa5dc2c03eebbfc299a6fda20560a6c47f5b3534; original global index 3742.
def localCycle00045 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 2 5, .distance 0 2, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 30 1, .triangle 7 0, .triangle 0 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 335b4fec4717c48a13f406f64b88f3e11058dc38fa7dc1cc192c8b237160ab47; original global index 3931.
def localCycle00046 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 3387f251b329b3e2105cecf2b3b44fc5be10aa62b260a83fd14d264f1715002b; original global index 3941.
def localCycle00047 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 364d3066685a62fc282f88c5cf61d084e9a65a1279f83a63c85cc52eb3cb95d0; original global index 4164.
def localCycle00048 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .triangle 23 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 366c1dbc0a8608714ae80495c14a9c50a899520776905a890db0c341af7999d3; original global index 4177.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 3737d6c28d4abfd9786af86f1865dccbc5acf6db0db00922236e0435477d0e91; original global index 4240.
def localCycle00050 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 2, .triangle 11 1, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 37928b2df279e95b3a3c12dfc249b797f28b6bb20f04258acdc5124ebbbc957a; original global index 4274.
def localCycle00051 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 0, .triangle 24 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 37c50da5a227d399eba1be1a70ba8cd58e9375947ca3c0b0ec93dfae0a5d123c; original global index 4289.
def localCycle00052 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 2, .triangle 8 0, .triangle 30 1, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 385a3341ccb03a3295cadd38bc5e925df0c790bc35d427236baa59e327422b29; original global index 4329.
def localCycle00053 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 8 0, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 399183be39d113a17b3a05eab3a841a17c5bc4cdda4ed3b2cce0d9718629ce99; original global index 4436.
def localCycle00054 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -1, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 13 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 3c44ecff6747dfd5f46499b517de51a36b4f7e03ac496c582e112338d8955dd1; original global index 4675.
def localCycle00055 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 2 1, .triangle 0 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 3cf9142a1a3142b3959b311eddb6fbe0f37c3e60ed6c9775f76488747ea6916b; original global index 4721.
def localCycle00056 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 3d4b1120274a2630565f6b9e7861c2333a5d8be69400e96b476f947924925b67; original global index 4748.
def localCycle00057 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 6 1, .gapLower 6 0]

-- Original cycle 4452ac49d5e35a27ce13c265d1644ad6c77909250b63211128804b4006f2b6ee; original global index 5289.
def localCycle00058 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 11 2, .gapLower 6 2, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaLower 3]

-- Original cycle 495d2cb62380a87f1769021660646e6bf6b315066ed7c09e856ba17e390fdb69; original global index 5685.
def localCycle00059 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 4 2, .gapLower 6 3, .gapUpper 1 3]

-- Original cycle 4adb6f35382054b689476600687f5deab66c015874ef1aeaf57e9955cbde174c; original global index 5813.
def localCycle00060 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 4 6, .distance 0 4, .distance 0 1]
    constant := ![0, -2, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true] }
  origin := ![.triangle 4 2, .gapLower 6 2, .triangle 23 1, .gapUpper 4 2, .triangle 2 1]

-- Original cycle 4de6dbcc97843240fed5c581297a9b62384bc31c2419d0341275608ddca18e1a; original global index 6049.
def localCycle00061 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 4e314d1e74bf636ad05e1619f45aa45f9dc0009a511069b7726407fc8e0745a9; original global index 6068.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 0, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 4fb6edf5c20d2771e5c0fe364d38c83cce9d0976bdae39be84d58a6110455a75; original global index 6190.
def localCycle00063 : Cycle where
  length := 3
  data := {
    node := ![.theta 5, .distance 5 6, .theta 6, .theta 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 0, .gapLower 6 0, .thetaNext 5]

-- Original cycle 50c9e5f343ac77a5f4e6a9e35be2069cc0d6843b190732de605cc64389cd6fdf; original global index 6274.
def localCycle00064 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 0 6, .distance 0 2]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .triangle 8 1]

-- Original cycle 51e3b58b12f14d47684be74ab0c3c8d47402bc46b295a67b3e91349f6d33ba7c; original global index 6371.
def localCycle00065 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 32 0, .triangle 23 0, .triangle 2 0, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .gapLower 3 0]

-- Original cycle 527e1bdef50d11fd04ca7ba942752fef2c3319238cc9c5178eb08a896aa0a691; original global index 6413.
def localCycle00066 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 0, .triangle 23 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 52ab866aacf7887e45da17144cde3b1fd5cc895ebb61c59e33dbfd44a174f98c; original global index 6425.
def localCycle00067 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 558abf280c22270e6470adacd0d39436db93925cac38e20e80e143dd0618a008; original global index 6626.
def localCycle00068 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 0, .triangle 20 1, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 5599f1fce4b8423fbf61aa07c27b07fd5e38f4e0b837ddc8a87a446be63f1f36; original global index 6637.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .gapLower 4 0]

-- Original cycle 56b8059df5cdd87a96a4c175c1b57ed354aea82e5737d53248b7ae4311f60fca; original global index 6722.
def localCycle00070 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 15 2, .triangle 21 0, .triangle 27 2, .triangle 29 1, .corridorLower 4 6]

-- Original cycle 574b58c443a060880ff59c7a55d957ac8a0404f591b1498c80ef966afaae34a2; original global index 6764.
def localCycle00071 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 0, .triangle 20 1, .triangle 21 0, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 58902c02faf498454b41fec2470e5a817035ca03334e3e03062c8de4fb69ec79; original global index 6874.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .triangle 14 1, .triangle 34 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5f0b501e8151cee45f4e07342ac14ef8f481a8c42052fda8d0727956193729dc; original global index 7401.
def localCycle00073 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 3, .triangle 4 1, .triangle 18 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 5fe1dabdd9f8b04f57eddc95c5536879813b30ed23c7906243c3ce0c189d7d5c; original global index 7474.
def localCycle00074 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 5fe982a97b314e0bff0fdf52270d161d6f44daf49c99951274b904bce232cb33; original global index 7477.
def localCycle00075 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 32 0, .triangle 29 0, .triangle 16 2, .triangle 2 0, .triangle 0 2, .triangle 7 0, .triangle 17 0, .triangle 15 0, .gapLower 3 0]

-- Original cycle 60dda3183b5fe504dc7c309061f97c4d99d4d91e13f67c456a8e07fb2f2e8e27; original global index 7550.
def localCycle00076 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 3]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .triangle 11 1]

-- Original cycle 618ea600dcc0d1bf975347752b669608b9600aa9ab134ae25f724cf3278c06f7; original global index 7611.
def localCycle00077 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 2, .triangle 4 0, .triangle 0 2, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 6620e6a611e669eb130282c4ce9903f1509e00e9d7ed01387b588a08b78340a2; original global index 7946.
def localCycle00078 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -3, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 67113837c8ad02ba0f789109b4df25af575db5c34f9ec98e4b1e24406d2d5138; original global index 8007.
def localCycle00079 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .triangle 14 0, .triangle 7 1]

-- Original cycle 671565b2b940b718e949091e61e3fb69accf25477169be87efbf05f94eb5f37f; original global index 8011.
def localCycle00080 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 68f8bb30bde52dd23ac7c3aa55376a4d83e4e9757ab19ccb506630709071b7e8; original global index 8166.
def localCycle00081 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 8 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 698af1f02b84b8a00977e8b2db6cfa0a5d54747e3ac2869874f997c9fceba94f; original global index 8207.
def localCycle00082 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle 6a9148faa71e032b4b42a7d399c88297d1dcf2555d40d2a7c31345e5dc4f0412; original global index 8298.
def localCycle00083 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 0, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 20 2, .triangle 22 1, .corridorLower 4 5]

-- Original cycle 6ab3333cf34d17238be3c076e424422aa2cf81cee0472eb3b7c50b605e25d376; original global index 8308.
def localCycle00084 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 6c52e8b35653e2608f7c5a7067ea69774d1f2198d445956673f994666b89604c; original global index 8439.
def localCycle00085 : Cycle where
  length := 5
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle 6eafa00388e01d13b50c50cc925c933b6fc3e2fcc04d9230084d6600fcc5ac79; original global index 8587.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .triangle 8 0, .triangle 0 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 7103bd161d2e99f3e49fc24b8bba2f772c4963686f0256fc66bbb433875e701d; original global index 8766.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 72b183f96ada198c554ae21232ec7a1981cee1688728591a21d3306f66c998b0; original global index 8879.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .triangle 3 0, .triangle 0 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 72fe0da38127ef77fb0f5747991fb12f87890beaac7a4176ebf096cc2a15ebd9; original global index 8909.
def localCycle00089 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 3, .gapLower 6 2, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 74a54efd84285c6fbcb3cb201afb25dac3615ecbd0f16e3689a519e5131502fb; original global index 9035.
def localCycle00090 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 0, .triangle 0 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 74ad577d607164e986dfffaf9118baf7eaa821ea176d581c8206e67b9f64a7d6; original global index 9040.
def localCycle00091 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 14 0, .triangle 30 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 764e7bdd4cfe4594de6d52f93e2d8ddaddc943905c0439e7258f5f23b362a50b; original global index 9157.
def localCycle00092 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 3]
    constant := ![2, -2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .triangle 14 0, .triangle 10 1]

-- Original cycle 76713f45e792b06477b6fe4dea84506edc921217872d9eb9069ee4c4f8c2a65f; original global index 9170.
def localCycle00093 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 10 1, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 768fe51fc5ec74f080e8f4065faeaea4d6e92376dc3df7acdd3eec1228d843cd; original global index 9176.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 10 1, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 79cf2fecad0aa8ae6fd9974beef5f43013fae86feafc220b6d64ea7aa194e82c; original global index 9422.
def localCycle00095 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 7abfb0ca7ed80dfd4a11872456bf4e30508b08d9c2933cd3174bcd416bb24b7b; original global index 9500.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 7ad8897c663d8cb95c157dae1e836c889920016cfbfb5e6e5eb5a10467e008d6; original global index 9511.
def localCycle00097 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 7 1, .triangle 8 0, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 7c7bdeaaaab41f0a532ada3fe3a9e00585e36a1db4491122b5f026fbfca393fa; original global index 9633.
def localCycle00098 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 21 2, .triangle 4 0, .triangle 0 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 7d4de7fa723578b0ff62af77602707617baafa847ad888c800a04673249b1387; original global index 9711.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 2 0, .triangle 3 0, .triangle 22 1, .corridorLower 4 5]

-- Original cycle 7d5f9b57e64d728a49530a8363855abd638e30701a181d1d6f9c007647600185; original global index 9718.
def localCycle00100 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 4 2, .gapLower 6 2, .gapUpper 1 4]

-- Original cycle 7ddd83272ce547a411c9669fc5fbe955b70ef93a241f45c22867e7b6de5339f4; original global index 9775.
def localCycle00101 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 3 2, .triangle 14 0, .triangle 34 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 7e6930487fba56c35cee65a2baf3a2d2b2916343564774a4c01dc36fc4a3a591; original global index 9819.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 18 2, .triangle 4 0, .triangle 3 0, .triangle 22 1, .corridorLower 4 5]

-- Original cycle 7ea3567dd23490630ae1cecec3f4e686346210db6d48268d1453284be7b79759; original global index 9831.
def localCycle00103 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 2 1, .triangle 0 2, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 83c46021227a0291c429f41e68a0d6436d7cc165b7f8e278bdedcbb351177837; original global index 10225.
def localCycle00104 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 2, .gapLower 6 3, .triangle 23 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 85ec940afc554b28622e25ffa31ea2572a115a2101a107f61bc7bb8aadde6cd4; original global index 10389.
def localCycle00105 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .gapLower 6 2, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 8693b4f107ad4b44ef51b153ff300a9a5f757ccb1e9971cfbae6997910784fd6; original global index 10434.
def localCycle00106 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 0, .triangle 23 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 878786a18295d8c20fa53786a882b3c3b30b956c48cb37d503eb040746ac2e89; original global index 10507.
def localCycle00107 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 10 1, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 88ad94c9f664a1a56bc549070760be7c30eb5402c15b78c64baebd7696b4f4b4; original global index 10590.
def localCycle00108 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 0, .triangle 7 0, .triangle 0 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 8e5f537528192d620e0a58215bd0158f52959b1678a924d1ad08271c4063abc3; original global index 11021.
def localCycle00109 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Original cycle 8f1657ca8184ca7adc7304a9b0b3baf6392b60307b4c89a5ed5c4dbd51921ecb; original global index 11071.
def localCycle00110 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 2, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 8f92cdd165594a3e11a682fcf5dbe9fbfffbaec80c52822fd9075f9ee7023c61; original global index 11112.
def localCycle00111 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 0, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 8fc44b3ebc97f12ba08f6eee9a136549735ae422576a82b0fd8b3e714950deeb; original global index 11127.
def localCycle00112 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 2 1, .triangle 3 0, .triangle 22 1, .corridorLower 4 5]

-- Original cycle 8ff35206b76948545dfd3423fd840bd9d0357a2580a0174eea9ae748d6c3ed3b; original global index 11144.
def localCycle00113 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 909debd3de1ad9e2a178ea89e2438f838f8a6b2b87d245526f819c572e68f684; original global index 11194.
def localCycle00114 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, 0, -2, -2, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 15 0, .gapLower 3 0]

-- Original cycle 916d0c8569c7e071ecac3deea6949edb458dbe9b74a14e0153cdde3c48038a13; original global index 11265.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .gapLower 4 0]

-- Original cycle 927684fd7f5546de276417ac3914fbf7b5b0e2287f68d1665c8a5d3306787ea8; original global index 11343.
def localCycle00116 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 0, .triangle 18 1, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 927d001131ffeebcbd28cfaa33318f6d6e7d195b853f016ab91c689f3de59c9b; original global index 11346.
def localCycle00117 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 21 2, .gapLower 6 2, .triangle 4 1, .triangle 3 0, .triangle 17 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 94c659b72a58c4a8dc53335ee29010e5be35f9e68691254fcb421cd090a86712; original global index 11546.
def localCycle00118 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -3, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 4 1, .triangle 18 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 955afde7b114b49c5839e93993535b063bf6f4e77f8a53e19ce22e6127425f65; original global index 11605.
def localCycle00119 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 0, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 95acb2f78a19cd10d292cd250528a3cc5ab3c820ebd85c08da900bd9d37bb243; original global index 11635.
def localCycle00120 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 2 0, .triangle 0 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 95e3837d29ff7af96dc98ba1bd5a0ccdbcb6d5937e093a77c4784052bafa593f; original global index 11653.
def localCycle00121 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 0, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 992ba3eb87b32009d809029c050cdcf4f59c96d55ae87d133f8f79aafb987d38; original global index 11893.
def localCycle00122 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, 0, -2, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 32 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 2, .triangle 4 1, .triangle 3 0, .triangle 17 1, .triangle 15 0, .gapLower 3 0]

-- Original cycle 99b7fac89cbb94fcae131e85b417565c2829209d2793169e9bf71c8a525d591d; original global index 11934.
def localCycle00123 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 3 2, .triangle 14 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 9a4812b79d44b7bcb6cbdec1a4bda1f22f8974bd3c8c2dd8786ec892dbe58f3b; original global index 11989.
def localCycle00124 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 9b68070bc2333872732e7a307861851762f9cdbd3035bac3cf39b300e3d12b82; original global index 12086.
def localCycle00125 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .triangle 23 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 9bbe41446a8dbca616038b2a65d53ccc3d8156886fe4bd205e56c3537f54f8fd; original global index 12116.
def localCycle00126 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 17 0, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 9bff84545b48bd6552206bd50d43b318fc368dcf1ad332b02f27d838d4f09b05; original global index 12134.
def localCycle00127 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 3 2, .triangle 14 2, .gapLower 6 2, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle a2c1e5cf1027158a142409caeb5914a61dd63dbe69906ece52e6013391157c83; original global index 12654.
def localCycle00128 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle a2c38ed8617e6e853056b47f789a8b301d733fe8c804fcce0f84dddc0406cd4f; original global index 12656.
def localCycle00129 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle a35647de1b715b5591d49e6d5db29235a7a8cb5e1611e09437b4bd035221b6c3; original global index 12696.
def localCycle00130 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .triangle 24 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Original cycle a3bed95ae11f9a9f26860410b9da6b1dd5b40bc7d13e5367251b013734669529; original global index 12734.
def localCycle00131 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle a769ab574754e874cd6a13065cfe8412ea92380d2f8fa34f9bfb4e0c397a6572; original global index 13025.
def localCycle00132 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 0, .triangle 23 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle a9707215f99a8e69d5fcd6ef958d61def534f35a301e1e20c240afc21aadd29c; original global index 13190.
def localCycle00133 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 3 6, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 33 1]

-- Original cycle aa36aa17a9f732f854e2002e05fc0927a8b4bf5dc330c2b39de03f9d4368ae22; original global index 13251.
def localCycle00134 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 4 2, .gapLower 6 2, .gapUpper 1 4]

-- Original cycle ab0dcbb40ad7ccb7f3a4ea4b928cf78eeb8963d4043420170ea1391324290d3e; original global index 13324.
def localCycle00135 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 2, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ad2b5ea8fa2dc350d673a0205c648ba0963e9390a1a54a257adbd9bdf402a8bc; original global index 13497.
def localCycle00136 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, 0, -2, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .triangle 17 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b20dcab7961cf48b54b5b84d19c6d2dea943bbf21a2e5e0b53d709121b0eb0bf; original global index 13912.
def localCycle00137 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 2 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b30b61fa1251965ecd84ddf4d63bf23a703170db0e2d7b106471c640ccc06ab6; original global index 13991.
def localCycle00138 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 3, .triangle 13 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle b8060c2870050827b672f74f8c7464566053c0d0194ef16c93788e85c2d39b9c; original global index 14357.
def localCycle00139 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, 0, -1, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 16 2, .triangle 2 0, .triangle 0 2, .triangle 7 0, .triangle 17 0, .triangle 15 0, .gapLower 3 0]

-- Original cycle b8366890c332bb30b688bba1d436de3bc3c64184d3db3e2757c1b88375f8937b; original global index 14373.
def localCycle00140 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 0, .triangle 17 1, .triangle 18 0, .triangle 29 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle b9fbca27b37630774f0179416a7e5dcc0ae4a18b7f63b4e09662bf3660a52e75; original global index 14523.
def localCycle00141 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 3]
    constant := ![2, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 18 2, .gapLower 6 3, .triangle 11 1]

-- Original cycle bb4ea16e59ed3cf5f323485959af0deda1d3800c94494be2e634f6a7aa19503e; original global index 14624.
def localCycle00142 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 0 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle be7ab9eb587fe5661a3eec6fcfe4ad6d8d5982609b7ad4db7db19822539fcedf; original global index 14862.
def localCycle00143 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 2 1, .triangle 0 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle bf0dd72e5a21cc87d09d18c6388f6eeb3247ab3acd5160b5a98c21b02ff7d5f0; original global index 14905.
def localCycle00144 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 7 1, .triangle 8 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle bff5a112b9688fe2a94ebd69687514bc8b74127f8e4b66a89450f7ff91d7b2ae; original global index 14982.
def localCycle00145 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 0, .triangle 20 1, .triangle 21 0, .triangle 27 2, .triangle 29 1, .corridorLower 4 6]

-- Original cycle c001d7055cd3870c9bbb5e72194f3bc03c3a0b7633d9b8d6e5b1cf125987adc9; original global index 14988.
def localCycle00146 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 3, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle c0c3032d875d1173bc0ae631ede6c53eb8f4d081d476c09e2b917b1005f39d7c; original global index 15051.
def localCycle00147 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .triangle 2 0, .triangle 3 0, .triangle 22 1, .corridorLower 4 5]

-- Original cycle c0d989c9da40157cecd83249b1ee5aa217a05d976323f1a40c5aaea30f9658e9; original global index 15056.
def localCycle00148 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .triangle 23 1, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle c183b76a50ba2f542107d4448343d1e37bf1495ac55872251c4ab5b962b0fad4; original global index 15114.
def localCycle00149 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle c43a2d6770d94ea4c7d78524484f166995da34f7791a6ca04ce12d165e6844b9; original global index 15310.
def localCycle00150 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 0, .triangle 3 0, .triangle 22 1, .corridorLower 4 5]

-- Original cycle c64602181ee08bc749d1255c8ae35b46162eb66e943a068699c076e48e24e75f; original global index 15462.
def localCycle00151 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .gapLower 6 2, .triangle 4 1, .triangle 3 0, .triangle 17 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c77d3737e805f7596261c1a7d9239bac9960894242517bd005b7e9c3ea98f2cf; original global index 15567.
def localCycle00152 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .triangle 14 0, .triangle 7 1]

-- Original cycle c81e152aed76a3d999ef1f69ebaf4c68504f9829792ee630613050e53d29f145; original global index 15622.
def localCycle00153 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![4, 0, 0, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle c951d2115d22c3f2379162d83fd1bfce23e52eea5fb857ccb14eaaa6575ea9a9; original global index 15739.
def localCycle00154 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle ca868b39fd710550e103f0cff8fb5ddf12861a56bc97e0a711d2f443deba6a38; original global index 15828.
def localCycle00155 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 21 2, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle cc26386f1a681c9a31be15e4ab125a8d89b050cda2a60e4272655c8170dd6d0c; original global index 15956.
def localCycle00156 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 2, .triangle 8 1, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle cd297c7b5cf1a010242b9413596474eff9f65b17aa6008f54a8ed074819ab034; original global index 16033.
def localCycle00157 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2]
    constant := ![2, -3, 0, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .triangle 4 2, .triangle 8 1]

-- Original cycle d158b39bde4b5a30be7918012ca0cc842ba5fd4faf99b8956f651ab3a51c006b; original global index 16342.
def localCycle00158 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle d222da60c63da2cd7eca4fb7a09c4ecaf7ce64dd4f824aae6d507386d5723d10; original global index 16397.
def localCycle00159 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 0 6, .distance 0 2]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .gapLower 6 3, .triangle 8 1]

-- Original cycle d26dfdd1db50de8c91698eab4dcccd1c362dc9d0a9956edf8e9e9bbcd68c91e6; original global index 16419.
def localCycle00160 : Cycle where
  length := 4
  data := {
    node := ![.theta 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 0, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d29fd8a486b265e0bbf361844f10639e0075c2002bc96a73cedf3768b316881b; original global index 16436.
def localCycle00161 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 2, .triangle 34 0, .corridorLower 4 5]

-- Original cycle d309afbd0b7c030d207dc7ea8cff3078e09db4b297836bc769b8af0fe1984552; original global index 16462.
def localCycle00162 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle d3ca438ad907f6358603c5bab95f53595d20511a13a1d2901f433a26fa40939a; original global index 16527.
def localCycle00163 : Cycle where
  length := 4
  data := {
    node := ![.theta 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 0, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d4fcf12dec055e4351b4e76363faf4dcd3d8b05c7cdb1c0005e976e66139df5a; original global index 16619.
def localCycle00164 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 2, .gapLower 6 2, .triangle 18 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle d6bb9c531a166652010a467beb50eae10a480169d767d1441bd4f757c8e44d8d; original global index 16761.
def localCycle00165 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 0, .triangle 0 2, .triangle 7 0, .triangle 17 2, .triangle 22 1, .corridorLower 4 5]

-- Original cycle d72545ed74e0c078dc7d650e416ec65f1d374f226061c2749f457ae02a6cb0da; original global index 16791.
def localCycle00166 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .triangle 34 0, .corridorLower 4 5]

-- Original cycle dac3f4e900ae5be4b1bd9357e658cb7c25cf993da2b76502c9a6e2a69f8c317b; original global index 17094.
def localCycle00167 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, -2, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 18 2, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle db3ab9c34f5b4f1f3dcd0ee1da60715a9ff069242aa1977e8cdce026ccf946d4; original global index 17134.
def localCycle00168 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle db3f0804d156b4f76ad83c9b1f328a8b49a4483009544675d636369364bebf9c; original global index 17137.
def localCycle00169 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 0 6, .distance 5 6, .distance 4 6, .distance 0 4]
    constant := ![0, 0, -2, -2, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.triangle 12 2, .triangle 14 2, .gapLower 6 2, .gapLower 6 1, .gapUpper 4 2]

-- Original cycle db605bd9fb690e173a9984420cd4331503a8f6c00a09a3fb659dfd859dcb3f3d; original global index 17148.
def localCycle00170 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 0 1]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 0 2, .gapUpper 2 3, .gapLower 6 4, .triangle 4 0]

-- Original cycle dc257873c2af2cf0e2882ab9796433415793a720b993385c9e883b49512c3b5d; original global index 17205.
def localCycle00171 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle dc9faa30ad1ad770ef77645528dae4d4aa36f45600d4f0b70a1b88306fa76be9; original global index 17237.
def localCycle00172 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 2 0, .triangle 3 0, .triangle 17 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle dda88e9fbc7d872f1299f021d351eec01964a8569c169dbf38b4b98f53b58fbb; original global index 17326.
def localCycle00173 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .triangle 24 0, .triangle 14 0, .triangle 3 1, .triangle 0 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle dde2ff24e095e20f2d7d8eb57ae786a7855ddf46865d49de10d7a900afe15816; original global index 17345.
def localCycle00174 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle e03596a03da6ed6ef0b52a8719b822f7e97ce39495da5282913d4b49c50d2ba2; original global index 17526.
def localCycle00175 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 0, .triangle 17 1, .triangle 18 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle e12de6ca108f24754e4d684cd16a7d52461f767f0dad14d677865510975f3601; original global index 17610.
def localCycle00176 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 1]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 1 4, .gapLower 6 2, .triangle 4 1]

-- Original cycle e159f998f86392472f21b54b768c2a0f491588588b46c571222ec9f4a2ab288f; original global index 17624.
def localCycle00177 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 0, .triangle 22 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle e1e3a15f977c14570cd5be138a1b4a64a02e5c87d3167eeda82aac5b18b63bac; original global index 17665.
def localCycle00178 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 3 6, .distance 3 5]
    constant := ![2, -2, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 33 1]

-- Original cycle e27dd4919367db123d843d7afc51256d824d674fe8df8e17ad288d7d0c4ad3be; original global index 17708.
def localCycle00179 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 10 1, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle e3491aad26563225524a09eaad21a99e70c1416d26329fa0f7b101429667274c; original global index 17774.
def localCycle00180 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .gapLower 6 3, .triangle 23 1, .corridorLower 4 6]

-- Original cycle e3ddc4456b2b47731774931c5a6a258e2df75a3e3cd8e891c413ac0d97dfcb86; original global index 17827.
def localCycle00181 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .triangle 30 1, .triangle 24 0, .triangle 17 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle e587a24b80c5221b4f1458074afb4746719cadd7c933731992032a61c0f1e570; original global index 17953.
def localCycle00182 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 0 2]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 5 2, .gapUpper 3 3, .gapLower 6 5, .triangle 8 0]

-- Original cycle e5df1403cab017b70e0e6e02cfcfe427bf7e71381e54545cafdd21f0ffb7900b; original global index 17984.
def localCycle00183 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .gapLower 6 3, .triangle 8 1]

-- Original cycle e6dbb5fb8bd0463af1c40b8e5d350e6a87c573e381492141cb6262ebf54195b8; original global index 18063.
def localCycle00184 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 4 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![2, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.gapUpper 4 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle e7dd7d2eda700f3b429a22aa5b9bf45f249dac2c5906173c4808b9c3acfb1029; original global index 18132.
def localCycle00185 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Original cycle e98f2e1590d0df1a647f6fd0ef5caecb60c11f6d36cc1a7ecedba2af9c1b4758; original global index 18250.
def localCycle00186 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 2 1, .triangle 0 2, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle e9e4b1d8c126ec0cbfa10602e381ecd21c170c7866ad5aba2e493f8d8aefb33f; original global index 18276.
def localCycle00187 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 5 6, .theta 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -2, 2, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 12 0, .triangle 34 0, .gapLower 6 0, .gapLower 6 6, .triangle 21 2, .triangle 4 0, .triangle 0 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle eb7228a65daca966a2ee1908058e8847d26528165f341d95cf1b2f47e553becc; original global index 18377.
def localCycle00188 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 0, .triangle 17 1, .triangle 15 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle ecf6ddb9936bc7d7d7078b04e87c6983a221aeb60d667fc9ea9b1a472a8c22e9; original global index 18497.
def localCycle00189 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 14 2, .gapLower 6 2, .gapUpper 5 2]

-- Original cycle ecf75f8bbc9ea2d49b1951795a2fa7b600b9eb9b5a8b601903fce3ef14450fb1; original global index 18498.
def localCycle00190 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 2, .triangle 24 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle ed203cb8589e1a1de944b8cd44ec43518a0dae0f15fbaf378846f6a4ac22df18; original global index 18513.
def localCycle00191 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .triangle 18 2, .gapLower 6 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle ed363cb2ab996d1adbf7be61e403265bd358a933112f9c8a4ae412c9366806f5; original global index 18521.
def localCycle00192 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![4, 0, 0, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle ee8dc13a3e98c76c09e03206aeea44c959cbe56e58b68b59c8f2aee260109a94; original global index 18615.
def localCycle00193 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 12 2, .triangle 14 2, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle ef53f5931e19f08760bdda218f3f9f20e0b2df06dbd90365cd6788905e94a963; original global index 18672.
def localCycle00194 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 14 0, .triangle 24 0, .triangle 22 1, .corridorLower 4 5]

-- Original cycle ef5d5c5fd2d4ad9e01486f472bd814bcff69178a8cae38c7a577974cbcc03183; original global index 18675.
def localCycle00195 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 14 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle f0e604f38b06ff6b56061d08882e90a0187917ef4cb82016664a1508e34efe73; original global index 18788.
def localCycle00196 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 4 6, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -2, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 0, .triangle 23 1, .gapLower 6 0, .gapLower 6 6, .triangle 30 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle f31e3988db02adb9f87f764e3187ab2e80deee72571857341cbe75a6253b8c34; original global index 18953.
def localCycle00197 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .gapLower 6 4, .triangle 4 1, .triangle 18 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle f545d15468e4d8cbe55cb2ca147f617574ee9c5cbb76224309a2baf7ad269262; original global index 19118.
def localCycle00198 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2]
    constant := ![4, 0, -2, -2, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.gapLower 2 6, .triangle 29 2, .gapLower 6 3, .gapLower 6 2, .triangle 4 1, .triangle 3 0, .triangle 17 1, .triangle 15 0, .corridorLower 2 3]

-- Original cycle f5569e90d778be6afdae1db3b164b16c589173640a6e4541785d6f6e8f97d179; original global index 19124.
def localCycle00199 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2]
    constant := ![4, 0, -2, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 2 6, .triangle 29 2, .gapLower 6 3, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 15 0, .corridorLower 2 3]

-- Original cycle f589b37e10b9b6df9b9ae281d7a936070253223e566b9f04864875d0c6c2a3a1; original global index 19144.
def localCycle00200 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![4, 0, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 0, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle f64cde32d1ce4710eac0027ecdfe00cff0d8ae4fc2c23fd9bf730a5f92b4fe76; original global index 19210.
def localCycle00201 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 2, .distance 2 3, .theta 2]
    constant := ![4, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 28 2, .triangle 30 0, .triangle 24 0, .triangle 3 0, .triangle 0 0, .triangle 15 0, .corridorLower 2 3]

-- Original cycle f7bd63c57dfce4a60c5a44252cda0d4206eb4ee4c7cd6f9581eaf27442495194; original global index 19314.
def localCycle00202 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 10 1, .triangle 11 0, .triangle 33 1, .triangle 30 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle fa40ff89021abc7dbedfa2418dccef4442a8bbefb7831030a5afd7ccf6c686e2; original global index 19518.
def localCycle00203 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle face39b8eee8c12b3026b0f3cff7ba03a59e3ff8f6ae2c5efe0ac923ec3f8cfe; original global index 19568.
def localCycle00204 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 2 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle fb7d9c2de09ba4d4b009123739c2e1da45a967f88f61f97896f4f367b86c22c4; original global index 19634.
def localCycle00205 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 2 1, .triangle 3 0, .triangle 22 1, .corridorLower 4 5]

-- Original cycle fbbf19f0b46721878f43eedfd37521d1c78b71d131c31207d0c2b1ffc26c560f; original global index 19654.
def localCycle00206 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 3]
    constant := ![2, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .triangle 4 2, .triangle 11 1]

-- Original cycle fcb2cc297b0129a9d07e3213fb79bdbe0b5216bc45959d8f7832f951a4099942; original global index 19744.
def localCycle00207 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 2, .gapLower 6 3, .triangle 18 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle fcd9caa66b7cc15150bd95a67792789260299c6a50d7afef4de0c7bc34ede1f5; original global index 19759.
def localCycle00208 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 21 2, .gapLower 6 3, .triangle 4 1, .triangle 0 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle fd6e79b4d4cf35935e86d0c93c8b6c606a80d80b19418441a5e74150e6529e18; original global index 19806.
def localCycle00209 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 2, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle ff7ab9ab3485e1bcb22745358a2b7fa4f5d4551b4ca74a577cd5f69d349ba23c; original global index 19975.
def localCycle00210 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 2, .triangle 11 1, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

def library : Library := fun id => if id < 105 then (if id < 52 then (if id < 26 then (if id < 13 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none))))) else (if id < 19 then (if id < 16 then (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none))) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)))) else (if id < 22 then (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none))) else (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)))))) else (if id < 39 then (if id < 32 then (if id < 29 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none))) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)))) else (if id < 35 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none))) else (if id < 37 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none)) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))))) else (if id < 45 then (if id < 42 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none)))) else (if id < 48 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none))) else (if id < 50 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))))))) else (if id < 78 then (if id < 65 then (if id < 58 then (if id < 55 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none))) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)))) else (if id < 61 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))) else (if id < 63 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none))))) else (if id < 71 then (if id < 68 then (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none))) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)))) else (if id < 74 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none))) else (if id < 76 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)))))) else (if id < 91 then (if id < 84 then (if id < 81 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none))) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)))) else (if id < 87 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none))) else (if id < 89 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none))))) else (if id < 98 then (if id < 94 then (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none))) else (if id < 96 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)))) else (if id < 101 then (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))) else (if id < 103 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)))))))) else (if id < 158 then (if id < 131 then (if id < 118 then (if id < 111 then (if id < 108 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none))) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)))) else (if id < 114 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none))) else (if id < 116 then (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none)) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none))))) else (if id < 124 then (if id < 121 then (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none))) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)))) else (if id < 127 then (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none))) else (if id < 129 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)))))) else (if id < 144 then (if id < 137 then (if id < 134 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none))) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)))) else (if id < 140 then (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none))) else (if id < 142 then (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none)) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none))))) else (if id < 151 then (if id < 147 then (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none))) else (if id < 149 then (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none)) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)))) else (if id < 154 then (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none))) else (if id < 156 then (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none)) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none))))))) else (if id < 184 then (if id < 171 then (if id < 164 then (if id < 161 then (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none))) else (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none)))) else (if id < 167 then (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none))) else (if id < 169 then (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none)) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none))))) else (if id < 177 then (if id < 174 then (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id = 173 then some localCycle00173 else none))) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none)))) else (if id < 180 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none))) else (if id < 182 then (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none)) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id = 183 then some localCycle00183 else none)))))) else (if id < 197 then (if id < 190 then (if id < 187 then (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none))) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none)))) else (if id < 193 then (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none))) else (if id < 195 then (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none)) else (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none))))) else (if id < 204 then (if id < 200 then (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none))) else (if id < 202 then (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none)) else (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id = 203 then some localCycle00203 else none)))) else (if id < 207 then (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id = 206 then some localCycle00206 else none))) else (if id < 209 then (if id < 208 then (if id = 207 then some localCycle00207 else none) else (if id = 208 then some localCycle00208 else none)) else (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id = 210 then some localCycle00210 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![3, 2, 1, 5, 4, 6], ![3, 2, 0, 5, 6, 4], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 1, 6, 2, 3], ![0, 4, 1, 5, 2, 3]], proof := .tail 201 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15872)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![3, 2, 1, 5, 4, 6], ![3, 2, 0, 6, 5, 4], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![0, 4, 5, 1, 2, 3]], proof := .tail 130 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15873)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![3, 2, 1, 5, 6, 4], ![3, 2, 0, 5, 6, 4], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 2, 3, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 88 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15874)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![3, 2, 1, 5, 6, 4], ![3, 2, 0, 5, 6, 4], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 2, 6, 3], ![4, 0, 1, 2, 5, 3]], proof := .tail 33 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15875)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![3, 2, 1, 5, 6, 4], ![3, 2, 0, 5, 6, 4], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 6, 2, 3], ![4, 0, 1, 5, 2, 3]], proof := .tail 201 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15876)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![3, 2, 1, 5, 6, 4], ![3, 2, 0, 6, 5, 4], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![4, 0, 5, 1, 2, 3]], proof := .tail 173 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15877)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![3, 2, 1, 6, 5, 4], ![3, 2, 0, 6, 5, 4], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 0, 1, 2, 3]], proof := .low6 (![101, 23, 189, 9, 157, 15, 98, 123, 16, 72, 170, 182, 56, 169, 21, 170, 182, 21, 89, 166, 161, 58, 183, 141, 208, 206, 170, 182]) }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15878)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![3, 2, 1, 6, 5, 4], ![3, 2, 0, 6, 5, 4], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 0, 1, 2, 3]], proof := .low6 (![63, 163, 193, 9, 157, 15, 98, 184, 127, 35, 170, 182, 187, 31, 138, 170, 182, 160, 171, 170, 182, 56, 183, 141, 208, 206, 170, 182]) }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15879)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![3, 2, 6, 1, 5, 4], ![3, 2, 6, 0, 5, 4], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 1, 0, 2, 3]], proof := .tail 51 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15880)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![3, 6, 2, 1, 5, 4], ![3, 2, 6, 0, 5, 4], ![3, 1, 6, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 1, 2, 0, 3]], proof := .tail 7 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15881)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![3, 6, 2, 1, 5, 4], ![3, 6, 2, 0, 5, 4], ![3, 6, 1, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 2, 1, 0, 3]], proof := .tail 174 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15882)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![6, 3, 2, 1, 5, 4], ![3, 2, 6, 0, 5, 4], ![3, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 1, 2, 3, 0]], proof := .tail 190 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15883)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![6, 3, 2, 1, 5, 4], ![3, 6, 2, 0, 5, 4], ![3, 6, 1, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 2, 1, 3, 0]], proof := .tail 174 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15884)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![6, 3, 2, 1, 5, 4], ![6, 3, 2, 0, 5, 4], ![3, 6, 1, 0, 5, 4], ![2, 6, 1, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 2, 3, 1, 0]], proof := .tail 32 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15885)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![6, 3, 2, 1, 5, 4], ![6, 3, 2, 0, 5, 4], ![6, 3, 1, 0, 5, 4], ![6, 2, 1, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 3, 2, 1, 0]], proof := .tail 2 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15886)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![3, 2, 6, 1, 5, 4], ![3, 2, 6, 0, 5, 4], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 1, 0, 2, 3]], proof := .low6 (![125, 132, 17, 59, 64, 15, 86, 148, 105, 104, 48, 182, 48, 10, 29, 66, 66, 66, 153, 111, 111, 111, 180, 182, 207, 76, 197, 182]) }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15887)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![3, 6, 2, 1, 5, 4], ![3, 2, 6, 0, 5, 4], ![3, 1, 6, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 39 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15888)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![3, 6, 2, 1, 5, 4], ![3, 6, 2, 0, 5, 4], ![3, 6, 1, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 43 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15889)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![6, 3, 2, 1, 5, 4], ![3, 2, 6, 0, 5, 4], ![3, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 135 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15890)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 3, 2, 1, 5, 4], ![3, 6, 2, 0, 5, 4], ![3, 6, 1, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 43 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15891)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 3, 2, 1, 5, 4], ![6, 3, 2, 0, 5, 4], ![3, 6, 1, 0, 5, 4], ![2, 6, 1, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 70 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15892)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 3, 2, 1, 5, 4], ![6, 3, 2, 0, 5, 4], ![6, 3, 1, 0, 5, 4], ![6, 2, 1, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 95 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15893)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![3, 2, 5, 1, 4, 6], ![3, 2, 5, 0, 4, 6], ![3, 1, 0, 5, 4, 6], ![2, 1, 0, 5, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 1, 0, 2, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 172 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15894)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![3, 2, 5, 1, 4, 6], ![3, 2, 5, 0, 4, 6], ![3, 1, 0, 5, 4, 6], ![2, 1, 0, 5, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 1, 0, 2, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 14 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15895)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![3, 2, 5, 1, 4, 6], ![3, 2, 5, 0, 4, 6], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 1, 0, 2, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 150 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15896)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![3, 2, 5, 1, 4, 6], ![3, 2, 5, 0, 6, 4], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 1, 0, 2, 3, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 205 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15897)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![3, 2, 5, 1, 6, 4], ![3, 2, 5, 0, 6, 4], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 0, 2, 3, 6], ![4, 0, 1, 2, 3, 5]], proof := .low6 (![54, 36, 176, 19, 30, 133, 27, 57, 191, 131, 102, 85, 61, 162, 113, 46, 1, 61, 198, 122, 117, 151, 114, 203, 199, 167, 102, 155]) }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15898)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![3, 2, 5, 1, 4, 6], ![3, 2, 5, 0, 4, 6], ![3, 1, 0, 5, 4, 6], ![2, 1, 0, 6, 5, 4], ![5, 0, 1, 2, 6, 3], ![4, 1, 0, 2, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 99 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15899)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![3, 2, 5, 1, 4, 6], ![3, 2, 5, 0, 4, 6], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 0, 1, 6, 2, 3], ![4, 1, 0, 2, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 99 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15900)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![3, 2, 5, 1, 4, 6], ![3, 2, 5, 0, 6, 4], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 1, 0, 2, 6, 3], ![0, 4, 1, 2, 5, 3]], proof := .tail 112 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15901)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![3, 2, 5, 1, 6, 4], ![3, 2, 5, 0, 6, 4], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 0, 2, 6, 3], ![4, 0, 1, 2, 5, 3]], proof := .tail 110 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15902)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![3, 2, 5, 1, 4, 6], ![3, 2, 5, 0, 4, 6], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 0, 1, 6, 2, 3], ![4, 1, 0, 6, 2, 3], ![0, 1, 4, 5, 2, 3]], proof := .tail 147 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15903)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![3, 2, 5, 1, 4, 6], ![3, 2, 5, 0, 6, 4], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 1, 0, 6, 2, 3], ![0, 4, 1, 5, 2, 3]], proof := .tail 22 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15904)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![3, 2, 5, 1, 6, 4], ![3, 2, 5, 0, 6, 4], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 0, 6, 2, 3], ![4, 0, 1, 5, 2, 3]], proof := .tail 209 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15905)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![3, 2, 5, 6, 1, 4], ![3, 2, 5, 6, 0, 4], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 0, 2, 3, 6], ![4, 1, 0, 2, 3, 5]], proof := .low6 (![20, 121, 100, 118, 78, 133, 108, 200, 134, 106, 82, 178, 196, 192, 8, 8, 28, 28, 124, 158, 60, 164, 42, 4, 136, 47, 45, 5]) }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15906)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![3, 2, 5, 6, 1, 4], ![3, 2, 5, 6, 0, 4], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 0, 2, 6, 3], ![4, 1, 0, 2, 5, 3]], proof := .tail 142 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15907)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![3, 2, 5, 6, 1, 4], ![3, 2, 5, 6, 0, 4], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 0, 6, 2, 3], ![4, 1, 0, 5, 2, 3]], proof := .low6 (![20, 121, 100, 26, 79, 15, 181, 200, 44, 119, 152, 182, 106, 192, 37, 8, 8, 28, 146, 152, 182, 164, 159, 0, 73, 92, 152, 182]) }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15908)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![3, 2, 6, 5, 1, 4], ![3, 2, 5, 6, 0, 4], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 6, 0, 2, 3], ![4, 1, 5, 0, 2, 3]], proof := .tail 194 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15909)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![3, 2, 6, 5, 1, 4], ![3, 2, 6, 5, 0, 4], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 1, 0, 2, 3]], proof := .tail 62 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15910)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![3, 6, 2, 5, 1, 4], ![3, 2, 5, 6, 0, 4], ![3, 1, 6, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 6, 0, 2, 3], ![4, 1, 5, 2, 0, 3]], proof := .tail 144 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15911)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![3, 6, 2, 5, 1, 4], ![3, 2, 6, 5, 0, 4], ![3, 1, 6, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 1, 2, 0, 3]], proof := .tail 62 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15912)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![3, 6, 2, 5, 1, 4], ![3, 6, 2, 5, 0, 4], ![3, 6, 1, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 2, 1, 0, 3]], proof := .tail 175 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15913)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![6, 3, 2, 5, 1, 4], ![3, 2, 5, 6, 0, 4], ![3, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 6, 0, 2, 3], ![4, 1, 5, 2, 3, 0]], proof := .tail 179 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15914)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![6, 3, 2, 5, 1, 4], ![3, 2, 6, 5, 0, 4], ![3, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 1, 2, 3, 0]], proof := .tail 62 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15915)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![6, 3, 2, 5, 1, 4], ![3, 6, 2, 5, 0, 4], ![3, 6, 1, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 2, 1, 3, 0]], proof := .tail 175 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15916)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![6, 3, 2, 5, 1, 4], ![6, 3, 2, 5, 0, 4], ![3, 6, 1, 0, 5, 4], ![2, 6, 1, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 2, 3, 1, 0]], proof := .tail 3 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15917)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 3, 2, 5, 1, 4], ![6, 3, 2, 5, 0, 4], ![6, 3, 1, 0, 5, 4], ![6, 2, 1, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 3, 2, 1, 0]], proof := .tail 6 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15918)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![3, 2, 6, 5, 1, 4], ![3, 2, 6, 5, 0, 4], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 1, 0, 2, 3]], proof := .tail 177 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15919)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![3, 6, 2, 5, 1, 4], ![3, 2, 6, 5, 0, 4], ![3, 1, 6, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 97 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15920)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![3, 6, 2, 5, 1, 4], ![3, 6, 2, 5, 0, 4], ![3, 6, 1, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 140 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15921)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![6, 3, 2, 5, 1, 4], ![3, 2, 6, 5, 0, 4], ![3, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 93 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15922)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![6, 3, 2, 5, 1, 4], ![3, 6, 2, 5, 0, 4], ![3, 6, 1, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 140 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15923)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![6, 3, 2, 5, 1, 4], ![6, 3, 2, 5, 0, 4], ![3, 6, 1, 0, 5, 4], ![2, 6, 1, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 71 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15924)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![6, 3, 2, 5, 1, 4], ![6, 3, 2, 5, 0, 4], ![6, 3, 1, 0, 5, 4], ![6, 2, 1, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 188 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15925)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![3, 5, 2, 1, 4, 6], ![3, 2, 5, 0, 4, 6], ![3, 1, 5, 0, 4, 6], ![2, 1, 0, 5, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 1, 2, 0, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 80 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15926)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![3, 5, 2, 1, 4, 6], ![3, 2, 5, 0, 4, 6], ![3, 1, 5, 0, 4, 6], ![2, 1, 0, 5, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 1, 2, 0, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 75 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15927)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![3, 5, 2, 1, 4, 6], ![3, 2, 5, 0, 4, 6], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 1, 2, 0, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 165 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15928)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![3, 5, 2, 1, 4, 6], ![3, 2, 5, 0, 6, 4], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 1, 2, 0, 3, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 103 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15929)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![3, 5, 2, 1, 6, 4], ![3, 2, 5, 0, 6, 4], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 0, 3, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 81 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15930)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![3, 5, 2, 1, 4, 6], ![3, 2, 5, 0, 4, 6], ![3, 1, 5, 0, 4, 6], ![2, 1, 0, 6, 5, 4], ![5, 0, 1, 2, 6, 3], ![4, 1, 2, 0, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 139 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15931)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![3, 5, 2, 1, 4, 6], ![3, 2, 5, 0, 4, 6], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 0, 1, 6, 2, 3], ![4, 1, 2, 0, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 99 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15932)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![3, 5, 2, 1, 4, 6], ![3, 2, 5, 0, 6, 4], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 1, 2, 0, 6, 3], ![0, 4, 1, 2, 5, 3]], proof := .tail 186 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15933)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![3, 5, 2, 1, 6, 4], ![3, 2, 5, 0, 6, 4], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 0, 6, 3], ![4, 0, 1, 2, 5, 3]], proof := .tail 77 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15934)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![3, 5, 2, 6, 1, 4], ![3, 2, 5, 6, 0, 4], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 0, 3, 6], ![4, 1, 0, 2, 3, 5]], proof := .tail 156 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15935)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![3, 5, 2, 6, 1, 4], ![3, 2, 5, 6, 0, 4], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 0, 6, 3], ![4, 1, 0, 2, 5, 3]], proof := .tail 128 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15936)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![3, 5, 6, 2, 1, 4], ![3, 2, 5, 6, 0, 4], ![3, 1, 5, 6, 0, 4], ![2, 1, 0, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 0, 3, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 52 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15937)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![3, 5, 6, 2, 1, 4], ![3, 2, 5, 6, 0, 4], ![3, 1, 5, 6, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 0, 6, 3], ![4, 1, 2, 0, 5, 3]], proof := .tail 52 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15938)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![3, 6, 5, 2, 1, 4], ![3, 2, 5, 6, 0, 4], ![3, 1, 5, 6, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 6, 0, 3], ![4, 1, 2, 5, 0, 3]], proof := .tail 91 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15939)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![3, 6, 5, 2, 1, 4], ![3, 2, 5, 6, 0, 4], ![3, 1, 6, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 6, 2, 0, 3], ![4, 1, 5, 2, 0, 3]], proof := .tail 13 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15940)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![3, 6, 5, 2, 1, 4], ![3, 2, 6, 5, 0, 4], ![3, 1, 6, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 1, 2, 0, 3]], proof := .tail 96 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15941)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![3, 6, 5, 2, 1, 4], ![3, 6, 2, 5, 0, 4], ![3, 6, 1, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 2, 1, 0, 3]], proof := .tail 69 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15942)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![3, 2, 5, 6, 0, 4], ![3, 1, 5, 6, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 6, 0, 3], ![4, 1, 2, 5, 3, 0]], proof := .tail 202 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15943)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![3, 2, 5, 6, 0, 4], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 6, 2, 0, 3], ![4, 1, 5, 2, 3, 0]], proof := .tail 13 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15944)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![3, 2, 6, 5, 0, 4], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 1, 2, 3, 0]], proof := .tail 96 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15945)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![3, 6, 2, 5, 0, 4], ![3, 6, 1, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 2, 1, 3, 0]], proof := .tail 69 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15946)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![6, 3, 2, 5, 0, 4], ![3, 6, 1, 5, 0, 4], ![2, 6, 1, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 2, 3, 1, 0]], proof := .tail 69 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15947)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![6, 3, 2, 5, 0, 4], ![6, 3, 1, 5, 0, 4], ![6, 2, 1, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 3, 2, 1, 0]], proof := .tail 109 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15948)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![3, 6, 5, 2, 1, 4], ![3, 2, 6, 5, 0, 4], ![3, 1, 6, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 87 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15949)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![3, 6, 5, 2, 1, 4], ![3, 6, 2, 5, 0, 4], ![3, 6, 1, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 41 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15950)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![3, 2, 6, 5, 0, 4], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 87 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15951)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![3, 6, 2, 5, 0, 4], ![3, 6, 1, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 41 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15952)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![6, 3, 2, 5, 0, 4], ![3, 6, 1, 5, 0, 4], ![2, 6, 1, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 41 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15953)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![6, 3, 2, 5, 0, 4], ![6, 3, 1, 5, 0, 4], ![6, 2, 1, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 129 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15954)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![3, 5, 2, 1, 4, 6], ![3, 5, 2, 0, 4, 6], ![3, 5, 1, 0, 4, 6], ![2, 1, 0, 5, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 2, 1, 0, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 204 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15955)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![3, 5, 2, 1, 4, 6], ![3, 5, 2, 0, 4, 6], ![3, 5, 1, 0, 4, 6], ![2, 1, 0, 5, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 2, 1, 0, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 120 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15956)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![3, 5, 2, 1, 4, 6], ![3, 5, 2, 0, 4, 6], ![3, 5, 1, 0, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 2, 1, 0, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 90 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15957)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![3, 5, 2, 1, 4, 6], ![3, 5, 2, 0, 6, 4], ![3, 5, 1, 0, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 1, 0, 3, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 143 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15958)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![3, 5, 2, 1, 6, 4], ![3, 5, 2, 0, 6, 4], ![3, 5, 1, 0, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 1, 0, 3, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 149 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15959)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![3, 5, 2, 1, 4, 6], ![3, 5, 2, 0, 4, 6], ![3, 5, 1, 0, 4, 6], ![2, 1, 0, 6, 5, 4], ![5, 0, 1, 2, 6, 3], ![4, 2, 1, 0, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 11 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15960)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![3, 5, 2, 1, 4, 6], ![3, 5, 2, 0, 4, 6], ![3, 5, 1, 0, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 0, 1, 6, 2, 3], ![4, 2, 1, 0, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 11 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15961)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![3, 5, 2, 1, 4, 6], ![3, 5, 2, 0, 6, 4], ![3, 5, 1, 0, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 1, 0, 6, 3], ![0, 4, 1, 2, 5, 3]], proof := .tail 55 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15962)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![3, 5, 2, 1, 6, 4], ![3, 5, 2, 0, 6, 4], ![3, 5, 1, 0, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 1, 0, 6, 3], ![4, 0, 1, 2, 5, 3]], proof := .tail 84 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15963)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![3, 5, 2, 6, 1, 4], ![3, 5, 2, 6, 0, 4], ![3, 5, 1, 0, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 1, 0, 3, 6], ![4, 1, 0, 2, 3, 5]], proof := .tail 116 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15964)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![3, 5, 2, 6, 1, 4], ![3, 5, 2, 6, 0, 4], ![3, 5, 1, 0, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 1, 0, 6, 3], ![4, 1, 0, 2, 5, 3]], proof := .tail 116 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15965)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![3, 5, 6, 2, 1, 4], ![3, 5, 2, 6, 0, 4], ![3, 5, 1, 6, 0, 4], ![2, 1, 0, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 1, 0, 3, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 34 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15966)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![3, 5, 6, 2, 1, 4], ![3, 5, 2, 6, 0, 4], ![3, 5, 1, 6, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 1, 0, 6, 3], ![4, 1, 2, 0, 5, 3]], proof := .tail 34 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15967)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![3, 6, 5, 2, 1, 4], ![3, 5, 2, 6, 0, 4], ![3, 5, 1, 6, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 1, 6, 0, 3], ![4, 1, 2, 5, 0, 3]], proof := .tail 195 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15968)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![3, 5, 6, 2, 1, 4], ![3, 5, 6, 2, 0, 4], ![3, 5, 6, 1, 0, 4], ![2, 1, 0, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 1, 0, 3, 6], ![4, 2, 1, 0, 3, 5]], proof := .tail 49 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15969)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![3, 5, 6, 2, 1, 4], ![3, 5, 6, 2, 0, 4], ![3, 5, 6, 1, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 1, 0, 6, 3], ![4, 2, 1, 0, 5, 3]], proof := .tail 49 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15970)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![3, 6, 5, 2, 1, 4], ![3, 5, 6, 2, 0, 4], ![3, 5, 6, 1, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 1, 6, 0, 3], ![4, 2, 1, 5, 0, 3]], proof := .tail 154 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15971)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![3, 6, 5, 2, 1, 4], ![3, 6, 5, 2, 0, 4], ![3, 5, 6, 1, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 6, 1, 0, 3], ![4, 2, 5, 1, 0, 3]], proof := .tail 62 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15972)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![3, 6, 5, 2, 1, 4], ![3, 6, 5, 2, 0, 4], ![3, 6, 5, 1, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 1, 0, 3], ![4, 5, 2, 1, 0, 3]], proof := .tail 24 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15973)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![3, 5, 2, 6, 0, 4], ![3, 5, 1, 6, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 1, 6, 0, 3], ![4, 1, 2, 5, 3, 0]], proof := .tail 107 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15974)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![3, 5, 6, 2, 0, 4], ![3, 5, 6, 1, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 1, 6, 0, 3], ![4, 2, 1, 5, 3, 0]], proof := .tail 94 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15975)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![3, 6, 5, 2, 0, 4], ![3, 5, 6, 1, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 6, 1, 0, 3], ![4, 2, 5, 1, 3, 0]], proof := .tail 62 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15976)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![3, 6, 5, 2, 0, 4], ![3, 6, 5, 1, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 1, 0, 3], ![4, 5, 2, 1, 3, 0]], proof := .tail 24 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15977)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![6, 3, 5, 2, 0, 4], ![3, 5, 6, 1, 0, 4], ![2, 6, 1, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 6, 1, 0, 3], ![4, 2, 5, 3, 1, 0]], proof := .tail 68 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15978)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![6, 3, 5, 2, 0, 4], ![3, 6, 5, 1, 0, 4], ![2, 6, 1, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 1, 0, 3], ![4, 5, 2, 3, 1, 0]], proof := .tail 24 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15979)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![6, 3, 5, 2, 0, 4], ![6, 3, 5, 1, 0, 4], ![6, 2, 1, 0, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 1, 0, 3], ![4, 5, 3, 2, 1, 0]], proof := .tail 168 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15980)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![3, 6, 5, 2, 1, 4], ![3, 6, 5, 2, 0, 4], ![3, 6, 5, 1, 0, 4], ![2, 1, 0, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 1, 0, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 126 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15981)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![3, 6, 5, 2, 0, 4], ![3, 6, 5, 1, 0, 4], ![2, 1, 6, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 1, 0, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 126 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15982)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![6, 3, 5, 2, 0, 4], ![3, 6, 5, 1, 0, 4], ![2, 6, 1, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 1, 0, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 145 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15983)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 3, 5, 2, 1, 4], ![6, 3, 5, 2, 0, 4], ![6, 3, 5, 1, 0, 4], ![6, 2, 1, 0, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 1, 0, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 38 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15984)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![3, 2, 5, 0, 4, 6], ![3, 1, 5, 0, 4, 6], ![2, 1, 5, 0, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 1, 2, 3, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 12 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15985)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![3, 2, 5, 0, 4, 6], ![3, 1, 5, 0, 4, 6], ![2, 1, 5, 0, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 1, 2, 3, 0, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 65 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15986)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![3, 2, 5, 0, 4, 6], ![3, 1, 5, 0, 6, 4], ![2, 1, 5, 0, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 1, 2, 3, 0, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 83 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15987)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![3, 2, 5, 0, 6, 4], ![3, 1, 5, 0, 6, 4], ![2, 1, 5, 0, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 1, 2, 3, 0, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 137 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15988)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![5, 3, 2, 1, 6, 4], ![3, 2, 5, 0, 6, 4], ![3, 1, 5, 0, 6, 4], ![2, 1, 5, 0, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 3, 0, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 53 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15989)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![5, 3, 2, 6, 1, 4], ![3, 2, 5, 6, 0, 4], ![3, 1, 5, 0, 6, 4], ![2, 1, 5, 0, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 3, 0, 6], ![4, 1, 0, 2, 3, 5]], proof := .tail 50 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15990)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![5, 3, 6, 2, 1, 4], ![3, 2, 5, 6, 0, 4], ![3, 1, 5, 6, 0, 4], ![2, 1, 5, 0, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 3, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 210 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15991)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![5, 6, 3, 2, 1, 4], ![3, 2, 5, 6, 0, 4], ![3, 1, 5, 6, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 3, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 18 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15992)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![3, 2, 5, 6, 0, 4], ![3, 1, 5, 6, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 3, 6, 0], ![4, 1, 2, 3, 5, 0]], proof := .tail 91 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15993)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![3, 2, 5, 6, 0, 4], ![3, 1, 5, 6, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 2, 6, 3, 0], ![4, 1, 2, 5, 3, 0]], proof := .tail 67 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15994)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![3, 2, 5, 6, 0, 4], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 1, 6, 2, 3, 0], ![4, 1, 5, 2, 3, 0]], proof := .tail 74 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15995)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![3, 2, 6, 5, 0, 4], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 2, 3, 0], ![4, 5, 1, 2, 3, 0]], proof := .tail 25 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15996)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![3, 6, 2, 5, 0, 4], ![3, 6, 1, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 2, 3, 0], ![4, 5, 2, 1, 3, 0]], proof := .tail 115 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15997)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![6, 3, 2, 5, 0, 4], ![3, 6, 1, 5, 0, 4], ![2, 6, 1, 5, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 2, 3, 0], ![4, 5, 2, 3, 1, 0]], proof := .tail 40 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15998)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![6, 3, 2, 5, 0, 4], ![6, 3, 1, 5, 0, 4], ![6, 2, 1, 5, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 1, 2, 3, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 185 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15999)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then
  (if offset < 32 then
  (if offset < 16 then
  (if offset < 8 then
  (if offset < 4 then
  (if offset < 2 then
  (if offset < 1 then
  (namedLeaf000) else
  (namedLeaf001)) else
  (if offset < 3 then
  (namedLeaf002) else
  (namedLeaf003))) else
  (if offset < 6 then
  (if offset < 5 then
  (namedLeaf004) else
  (namedLeaf005)) else
  (if offset < 7 then
  (namedLeaf006) else
  (namedLeaf007)))) else
  (if offset < 12 then
  (if offset < 10 then
  (if offset < 9 then
  (namedLeaf008) else
  (namedLeaf009)) else
  (if offset < 11 then
  (namedLeaf010) else
  (namedLeaf011))) else
  (if offset < 14 then
  (if offset < 13 then
  (namedLeaf012) else
  (namedLeaf013)) else
  (if offset < 15 then
  (namedLeaf014) else
  (namedLeaf015))))) else
  (if offset < 24 then
  (if offset < 20 then
  (if offset < 18 then
  (if offset < 17 then
  (namedLeaf016) else
  (namedLeaf017)) else
  (if offset < 19 then
  (namedLeaf018) else
  (namedLeaf019))) else
  (if offset < 22 then
  (if offset < 21 then
  (namedLeaf020) else
  (namedLeaf021)) else
  (if offset < 23 then
  (namedLeaf022) else
  (namedLeaf023)))) else
  (if offset < 28 then
  (if offset < 26 then
  (if offset < 25 then
  (namedLeaf024) else
  (namedLeaf025)) else
  (if offset < 27 then
  (namedLeaf026) else
  (namedLeaf027))) else
  (if offset < 30 then
  (if offset < 29 then
  (namedLeaf028) else
  (namedLeaf029)) else
  (if offset < 31 then
  (namedLeaf030) else
  (namedLeaf031)))))) else
  (if offset < 48 then
  (if offset < 40 then
  (if offset < 36 then
  (if offset < 34 then
  (if offset < 33 then
  (namedLeaf032) else
  (namedLeaf033)) else
  (if offset < 35 then
  (namedLeaf034) else
  (namedLeaf035))) else
  (if offset < 38 then
  (if offset < 37 then
  (namedLeaf036) else
  (namedLeaf037)) else
  (if offset < 39 then
  (namedLeaf038) else
  (namedLeaf039)))) else
  (if offset < 44 then
  (if offset < 42 then
  (if offset < 41 then
  (namedLeaf040) else
  (namedLeaf041)) else
  (if offset < 43 then
  (namedLeaf042) else
  (namedLeaf043))) else
  (if offset < 46 then
  (if offset < 45 then
  (namedLeaf044) else
  (namedLeaf045)) else
  (if offset < 47 then
  (namedLeaf046) else
  (namedLeaf047))))) else
  (if offset < 56 then
  (if offset < 52 then
  (if offset < 50 then
  (if offset < 49 then
  (namedLeaf048) else
  (namedLeaf049)) else
  (if offset < 51 then
  (namedLeaf050) else
  (namedLeaf051))) else
  (if offset < 54 then
  (if offset < 53 then
  (namedLeaf052) else
  (namedLeaf053)) else
  (if offset < 55 then
  (namedLeaf054) else
  (namedLeaf055)))) else
  (if offset < 60 then
  (if offset < 58 then
  (if offset < 57 then
  (namedLeaf056) else
  (namedLeaf057)) else
  (if offset < 59 then
  (namedLeaf058) else
  (namedLeaf059))) else
  (if offset < 62 then
  (if offset < 61 then
  (namedLeaf060) else
  (namedLeaf061)) else
  (if offset < 63 then
  (namedLeaf062) else
  (namedLeaf063))))))) else
  (if offset < 96 then
  (if offset < 80 then
  (if offset < 72 then
  (if offset < 68 then
  (if offset < 66 then
  (if offset < 65 then
  (namedLeaf064) else
  (namedLeaf065)) else
  (if offset < 67 then
  (namedLeaf066) else
  (namedLeaf067))) else
  (if offset < 70 then
  (if offset < 69 then
  (namedLeaf068) else
  (namedLeaf069)) else
  (if offset < 71 then
  (namedLeaf070) else
  (namedLeaf071)))) else
  (if offset < 76 then
  (if offset < 74 then
  (if offset < 73 then
  (namedLeaf072) else
  (namedLeaf073)) else
  (if offset < 75 then
  (namedLeaf074) else
  (namedLeaf075))) else
  (if offset < 78 then
  (if offset < 77 then
  (namedLeaf076) else
  (namedLeaf077)) else
  (if offset < 79 then
  (namedLeaf078) else
  (namedLeaf079))))) else
  (if offset < 88 then
  (if offset < 84 then
  (if offset < 82 then
  (if offset < 81 then
  (namedLeaf080) else
  (namedLeaf081)) else
  (if offset < 83 then
  (namedLeaf082) else
  (namedLeaf083))) else
  (if offset < 86 then
  (if offset < 85 then
  (namedLeaf084) else
  (namedLeaf085)) else
  (if offset < 87 then
  (namedLeaf086) else
  (namedLeaf087)))) else
  (if offset < 92 then
  (if offset < 90 then
  (if offset < 89 then
  (namedLeaf088) else
  (namedLeaf089)) else
  (if offset < 91 then
  (namedLeaf090) else
  (namedLeaf091))) else
  (if offset < 94 then
  (if offset < 93 then
  (namedLeaf092) else
  (namedLeaf093)) else
  (if offset < 95 then
  (namedLeaf094) else
  (namedLeaf095)))))) else
  (if offset < 112 then
  (if offset < 104 then
  (if offset < 100 then
  (if offset < 98 then
  (if offset < 97 then
  (namedLeaf096) else
  (namedLeaf097)) else
  (if offset < 99 then
  (namedLeaf098) else
  (namedLeaf099))) else
  (if offset < 102 then
  (if offset < 101 then
  (namedLeaf100) else
  (namedLeaf101)) else
  (if offset < 103 then
  (namedLeaf102) else
  (namedLeaf103)))) else
  (if offset < 108 then
  (if offset < 106 then
  (if offset < 105 then
  (namedLeaf104) else
  (namedLeaf105)) else
  (if offset < 107 then
  (namedLeaf106) else
  (namedLeaf107))) else
  (if offset < 110 then
  (if offset < 109 then
  (namedLeaf108) else
  (namedLeaf109)) else
  (if offset < 111 then
  (namedLeaf110) else
  (namedLeaf111))))) else
  (if offset < 120 then
  (if offset < 116 then
  (if offset < 114 then
  (if offset < 113 then
  (namedLeaf112) else
  (namedLeaf113)) else
  (if offset < 115 then
  (namedLeaf114) else
  (namedLeaf115))) else
  (if offset < 118 then
  (if offset < 117 then
  (namedLeaf116) else
  (namedLeaf117)) else
  (if offset < 119 then
  (namedLeaf118) else
  (namedLeaf119)))) else
  (if offset < 124 then
  (if offset < 122 then
  (if offset < 121 then
  (namedLeaf120) else
  (namedLeaf121)) else
  (if offset < 123 then
  (namedLeaf122) else
  (namedLeaf123))) else
  (if offset < 126 then
  (if offset < 125 then
  (namedLeaf124) else
  (namedLeaf125)) else
  (if offset < 127 then
  (namedLeaf126) else
  (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (15872 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 15872 ≤ id.val) (hhigh : id.val < 16000) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 15872)) = true := by
  let j : Fin 128 := ⟨id.val - 15872, by omega⟩
  have hsum : 15872 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (15872 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard124
