import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard162
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

-- Original cycle 017cd4f53c1a3fab84647abebec28672a8c25ce4f790bf3e587d34a2434773d6; original global index 124.
def localCycle00001 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 03380c4c311898c8a6b779fcbe89fde34e263fae08f734ee2a086b566861af63; original global index 259.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 27 2, .triangle 30 1, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 061dfbd8e51f32209bf2880a858cc1d1a26ef13d6b5ceb09b63afbc2fa9e6c54; original global index 505.
def localCycle00003 : Cycle where
  length := 3
  data := {
    node := ![.theta 0, .distance 0 1, .theta 1, .theta 0]
    constant := ![2, -2, 0]
    coefficient := ![1, -1, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 6, .gapUpper 1 6, .thetaNext 0]

-- Original cycle 06ca9d32a2628776cf635cb536d17772689ecb40f1fd48061e1fdad39c8fb58a; original global index 559.
def localCycle00004 : Cycle where
  length := 15
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, 3, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 085fd3585f8c10d8f26929089f8b4242a04c24c1ae0994b11f11aea25cbf8563; original global index 665.
def localCycle00005 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 086940d0c6edd260c70bd6a54771751243e0ee907de89a9da930a380aef68c7f; original global index 669.
def localCycle00006 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 08ad001d798436b1e8f28701abfd6da14d722390edf10ea9b00f23110703ac53; original global index 693.
def localCycle00007 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 0 5, .distance 0 3]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 5 4, .gapLower 0 1]

-- Original cycle 08ec8deb794aa4350b5d0f529c0dd83d3de54963ccccb7f0e93f34fa47bedbcc; original global index 711.
def localCycle00008 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .gapLower 3 0]

-- Original cycle 08ef20bacdfdb2dd4d4923fcc1ee3d1f59373c4161a3d118f4c4a4cf6b55e5a4; original global index 712.
def localCycle00009 : Cycle where
  length := 17
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 3, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 17 0, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 10 1, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 092542769fa3337a1b5e754c18bc0a0a23a722443ae5e96dc5892bafb65d1945; original global index 730.
def localCycle00010 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 092e7a3461a55e47cfe3ba518977943b58a6c3846e7d95095ba95138d0d6514e; original global index 735.
def localCycle00011 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 09aa8c751b0bb7a7625793ec7e3bb2df5a8593c3760b01af1625b1790faa0a3f; original global index 771.
def localCycle00012 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 3]
    constant := ![2, -3, 0, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 8 2, .triangle 11 1]

-- Original cycle 0a1815b80555f571cec55a99d01ef283033d8e472e4159c3f01265f97aa07ca4; original global index 814.
def localCycle00013 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 3 4]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 3 4, .gapUpper 5 5, .gapLower 6 5, .triangle 32 0]

-- Original cycle 0a3152fdd792a42fba9202bcf0832afe081ed363a04e1427c9875d45dcbd692d; original global index 819.
def localCycle00014 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 17 2, .triangle 20 1, .triangle 21 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 0ac21512c6f16ab63f5a6e380617b2e7525124575c962c053faeb52fba06ebfe; original global index 860.
def localCycle00015 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 0bc893ef557923e3f0a55d09109122a72d164012ae0f9bc766c37e49eee50cfd; original global index 940.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 0c80827b77617bb33757fa86e671f3ef5c83ddf730ca84f21e612abaca4e4e1e; original global index 990.
def localCycle00017 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .gapLower 6 0]

-- Original cycle 0c8bd5c71b94c4724322fce4a26c8c9ad699afcfef29a92e3b137fe32213ddee; original global index 993.
def localCycle00018 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .triangle 8 2, .triangle 4 1, .gapLower 6 1, .gapLower 6 0]

-- Original cycle 0f2191feeb5c52897de6910d42b91568a34190a2337b9c3a67e925590976b491; original global index 1203.
def localCycle00019 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 2, .gapLower 6 2, .triangle 18 1, .triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 0fdf80d1d692b04968301b326171a16fe3c1c2275f928c04e6b7950b74c4c81a; original global index 1265.
def localCycle00020 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 0 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .gapLower 0 3, .triangle 14 1, .triangle 10 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 102094c6c296eaa315e5a5bdc4b305e662788abd059ac6552c7fa0f145758d89; original global index 1292.
def localCycle00021 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 6 1, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 12bef9c0274ad8b46fbfa674b55064c3ad246e762e5c2350da4503092a586b9f; original global index 1478.
def localCycle00022 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, -1, 0, 3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 22 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 13a00d6812dbb6fb1fe1dc1fa97caae71969b1eeab626802fbb9309cee1e46d2; original global index 1549.
def localCycle00023 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 141673a13ba22b9d3041ab2da9e9540882fdc19c2ff630027618b23a8a77424f; original global index 1585.
def localCycle00024 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 15 2, .triangle 21 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 147eb31e44222dc90d8448c150f54ee2131f05ad9b8e76c0bea01c0b14012d8e; original global index 1623.
def localCycle00025 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 14 0, .triangle 10 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 16a240a63c007920c486f6fee79f703fa7b226d6ee9bb47736364f65b1342651; original global index 1774.
def localCycle00026 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 3 5]
    constant := ![2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, true] }
  origin := ![.gapUpper 5 5, .triangle 34 2, .gapLower 6 4, .triangle 33 1]

-- Original cycle 17d5579bbd60659f2ec2107d5e095f6f6145d57abd6eeb09128707af07134653; original global index 1862.
def localCycle00027 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 8 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 1874005b9ab5c9f133ed6b58d2b6a89535d4d4741074b564da795405dbdd67da; original global index 1915.
def localCycle00028 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 3, .gapLower 6 3, .triangle 14 1]

-- Original cycle 18cc650ba7bbd4f5eba0f3f82f265e4f1b2386f537d249ef21618efbda8cfdde; original global index 1938.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 14 2, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 19b1f8a16adf507348ec91368930473913f9ccf730679da2f5b4e99eda77b63a; original global index 2007.
def localCycle00030 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 1a4c1c685c9b39dbbe57dd324e2e2b8f415e21a6be261ffb011d53f6019525c8; original global index 2054.
def localCycle00031 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 1fcb7d40adc620433ca66c39c04d5cbac3da2d61e32c9ee4a7f2893cac166a3e; original global index 2442.
def localCycle00032 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .theta 6, .distance 5 6, .distance 3 5, .distance 2 5, .distance 0 2, .distance 1 2, .theta 1]
    constant := ![3, -1, -1, -2, 2, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .gapLower 6 0, .gapLower 6 6, .triangle 33 0, .triangle 26 2, .triangle 7 0, .triangle 0 1, .corridorLower 1 2]

-- Original cycle 2313ea455580a53a1c95aa728690a330722a272aea5d4676cac526d1c12f2026; original global index 2692.
def localCycle00033 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 16 1, .triangle 17 0, .triangle 28 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Original cycle 287ebcfa86ef467476633cb2a2193d4cc6a318dc2023126a9ba7e6f31ac0a3cd; original global index 3102.
def localCycle00034 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 3 5]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 33 1]

-- Original cycle 293115ead8bf0cf39adecee9e6668898fb268a3be931ceeaee384cd0a5fa19e8; original global index 3143.
def localCycle00035 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 0 1]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 5, .gapLower 4 3, .gapUpper 1 5]

-- Original cycle 2a41f9067e5f9db70bbaa25d00ed392488a12a63de97287151354518a5ee3394; original global index 3218.
def localCycle00036 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 2aa59bd67a9016760d57f06eacf5dfd7975f0103bc0d94926a02e8c71d9629c5; original global index 3244.
def localCycle00037 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 2ac5c93fc7065b4d6e816254af4a84d083ed769552a2176509d4a755363e575c; original global index 3256.
def localCycle00038 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 0 5, .distance 0 3]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 5 4, .gapLower 0 1]

-- Original cycle 2b7b98848b920da2b7f8c60f9593ae6e9968488c34b986d2f06700a4067940a8; original global index 3324.
def localCycle00039 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, 0, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 2, .triangle 18 1, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 2bd1c648861179db09d52db70f10b0617d801ac11c12892f74dd525921b5e8d7; original global index 3354.
def localCycle00040 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 2e1633e05f967cf8258391e23e392c21fc13c754d9ac54d9441adfe17d340c05; original global index 3521.
def localCycle00041 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 2e366c49bfa150e4fadef74341a735a095235af84407f7ed2a2a61ec0f3ea06e; original global index 3530.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 2f21ff58d33f74a8ae10865437877b9d406b02a56bc91f2c39d54eff91543ab3; original global index 3604.
def localCycle00043 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .triangle 8 2, .gapLower 6 2, .triangle 23 1, .gapLower 6 0]

-- Original cycle 2f820611cdecb6a89717a06a7ca09d1552e21cbf29d4d2bf473fb05455374a5e; original global index 3629.
def localCycle00044 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 29 1, .corridorLower 4 6]

-- Original cycle 2fa306225a76f2c755a137f0dd2416606fe7eb2a46f25e58ceced0339a210c3a; original global index 3640.
def localCycle00045 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -3, 3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 30406780557f7d32cb80e076280f7ef8fb6cbb40ac2c37e8f191ea50d3c686a4; original global index 3672.
def localCycle00046 : Cycle where
  length := 3
  data := {
    node := ![.theta 0, .distance 0 1, .theta 1, .theta 0]
    constant := ![1, -2, 0]
    coefficient := ![1, -1, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 6, .gapUpper 1 6, .thetaNext 0]

-- Original cycle 304301f493f3674b72c3e2162df5835a0ce78393af680d3f1cf34a7ede376603; original global index 3674.
def localCycle00047 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 305a6a170ee4c2a526d9488b97382373c68cc40e512c2d0426569c61af462390; original global index 3681.
def localCycle00048 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .theta 6, .theta 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -2, 0, 3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .gapLower 6 0, .thetaNext 5, .corridorUpper 3 5, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 17 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 311505cd80e9be0f5dfa6210fa5dc2c03eebbfc299a6fda20560a6c47f5b3534; original global index 3742.
def localCycle00049 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 2 5, .distance 0 2, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 30 1, .triangle 7 0, .triangle 0 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 32c0ed177b60dd9552575b0a46d8b1e8daa4c29d5ed93798d3740d6d992d271d; original global index 3886.
def localCycle00050 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .theta 1]
    constant := ![3, -1, -2, 3, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 27 2, .gapUpper 2 6, .thetaNext 1]

-- Original cycle 32e3a450cf79951b6053131a9af09cd1055057a481cc206a9af0a501055af54b; original global index 3898.
def localCycle00051 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 10 1, .triangle 11 0, .triangle 33 1, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 3387f251b329b3e2105cecf2b3b44fc5be10aa62b260a83fd14d264f1715002b; original global index 3941.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 35f715563e92c1f36bbf00633ca77297aa566380088e9d217fd531e53dbaf0d7; original global index 4142.
def localCycle00053 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, 0, 0, -2, 0, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .gapLower 6 2, .triangle 4 1, .triangle 23 1, .triangle 16 1, .triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 378221eda60d043258cadaa4772ba8b57d444e511ecfb322e24512a46496d3fc; original global index 4267.
def localCycle00054 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .theta 6, .theta 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -3, 0, 3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .gapLower 6 0, .thetaNext 5, .corridorUpper 3 5, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 38611d3fac1a615763294e62a8c4017c888915d783989ca4b3e6c7d34e4ebdca; original global index 4336.
def localCycle00055 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 27 0, .gapLower 3 0]

-- Original cycle 3b9a922c34e93b43374b507fa83bce3bbbf684931c56ff0c713395d108168766; original global index 4605.
def localCycle00056 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 27 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 3bc4113a061878ab7c4d59ccfbc055bdd42eb0c252dd362562660dc71e628de8; original global index 4622.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 16 1, .triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 3d6cadad86822adccaca46989575f8bb814f87122b87c63890ae045edf71e4cf; original global index 4757.
def localCycle00058 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -2, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Original cycle 3d93ac90057f6c0f8bfb0725d45b5410e6ac949eac5d595b019cc977928d7858; original global index 4767.
def localCycle00059 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 8 2, .gapLower 6 1, .gapLower 6 0]

-- Original cycle 3fdcab9c9833db8b4892fee0908f6c8655551f9f70ab1306c83b6d63576f8e99; original global index 4929.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -1, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 2 0, .triangle 16 1, .triangle 18 0, .triangle 30 1, .triangle 26 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 40be53d2f4aaea1e0bb663619090947492486f38614bd015e60e9c32da4292c2; original global index 5002.
def localCycle00061 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 435aeb1c47ca860bc820dfa839e216b69ada7054cf697ad56ad2f06608b9172e; original global index 5198.
def localCycle00062 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 2 1, .triangle 16 1, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 49828d662d223f127d81ec7a3494aba57f5cc2fc13591400e07445a92eec6ec4; original global index 5699.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 0 5, .distance 1 5, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 2, .gapLower 0 2, .gapLower 5 3, .triangle 17 1, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 49ac2133765d0944122d076bc6e6f5f9bf0206081c0043e43512a7397afff7fb; original global index 5714.
def localCycle00064 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 0 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 4a4116ff7dc070082c29abf7f7fb99741858704f71377b018b842dc979a809f0; original global index 5760.
def localCycle00065 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .gapLower 3 0]

-- Original cycle 4b9a4502a93e6dd9df2b73d37492ea7ff555f39889198c0c86e23b80834830c1; original global index 5866.
def localCycle00066 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 10 1, .triangle 11 0, .triangle 21 2, .triangle 24 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 4df24d344abb2c290be18dc11459a59c3b6faaf9d195d0020736bae7188a0add; original global index 6053.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 2, .distance 1 2, .distance 2 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -2, -2, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .gapLower 0 4, .gapLower 2 4, .triangle 18 0, .triangle 30 1, .triangle 26 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 52ab866aacf7887e45da17144cde3b1fd5cc895ebb61c59e33dbfd44a174f98c; original global index 6425.
def localCycle00068 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 52d28bc571c8ae6f706bc981daaa1a618bb14bc85782b2c66fbfde75738a0790; original global index 6447.
def localCycle00069 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .gapLower 6 2, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 5599f1fce4b8423fbf61aa07c27b07fd5e38f4e0b837ddc8a87a446be63f1f36; original global index 6637.
def localCycle00070 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .gapLower 4 0]

-- Original cycle 56004518c65f60aac00eff074008988c66f1b3c13e541fb2d8c4460d08035cea; original global index 6671.
def localCycle00071 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 571e8adc6f5027a4130092d53eb6bc38bca596df09862aee8a6940dbd87a463e; original global index 6752.
def localCycle00072 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 5 4, .triangle 14 2, .gapLower 0 2]

-- Original cycle 5970b4faea7d052e9e69fe5dc6b37fe76e069faacc7d95872143ecb9158d40dc; original global index 6947.
def localCycle00073 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 10 1, .triangle 11 0, .triangle 27 2, .triangle 29 1, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Original cycle 5e0b037f97b1c46a0ff87608ff8d08285e641a3fdc22aa194bb1341679461e9f; original global index 7314.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .gapLower 6 2, .triangle 18 1, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 5f0b501e8151cee45f4e07342ac14ef8f481a8c42052fda8d0727956193729dc; original global index 7401.
def localCycle00075 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 3, .triangle 4 1, .triangle 18 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 5f974b5b2bc7cdc0023e0a820d798ca0ccf321705c9c310b17562d9c9e5a7f95; original global index 7444.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -3, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 2, .gapLower 6 2, .triangle 18 1, .triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 5fa9d18cbef3fef2d70d3d590251875a367aec2aba58f1d3e384891b52bc6327; original global index 7452.
def localCycle00077 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 5, .distance 0 3]
    constant := ![2, 0, 0, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, true, false] }
  origin := ![.gapUpper 3 3, .triangle 11 2, .triangle 14 1, .gapLower 0 1]

-- Original cycle 5fe1dabdd9f8b04f57eddc95c5536879813b30ed23c7906243c3ce0c189d7d5c; original global index 7474.
def localCycle00078 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 6109de90692ff995403d2697fc745e0869d61a04fbee4f8d5d2f080880d630c4; original global index 7566.
def localCycle00079 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, -2, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 1, .triangle 18 1, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 6277a99164ad5d7c3f2fa9d46601dd27f80e396cfc448f66e559fa7734f54d0a; original global index 7683.
def localCycle00080 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 6620e6a611e669eb130282c4ce9903f1509e00e9d7ed01387b588a08b78340a2; original global index 7946.
def localCycle00081 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -3, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 6635e89e45b03f5364fb02a7469753b7273631c0598026dbf27de8f6be4f5e68; original global index 7951.
def localCycle00082 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, 0, -2, 0, 0, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, true, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .triangle 17 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 67113837c8ad02ba0f789109b4df25af575db5c34f9ec98e4b1e24406d2d5138; original global index 8007.
def localCycle00083 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .triangle 14 0, .triangle 7 1]

-- Original cycle 671565b2b940b718e949091e61e3fb69accf25477169be87efbf05f94eb5f37f; original global index 8011.
def localCycle00084 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 676b0aa6bf480f0ef3819e5bb296289f49b20ccf7a075650992a825bfc10cb94; original global index 8038.
def localCycle00085 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 2 5, .gapLower 4 4, .gapLower 0 4]

-- Original cycle 68f8bb30bde52dd23ac7c3aa55376a4d83e4e9757ab19ccb506630709071b7e8; original global index 8166.
def localCycle00086 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 8 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 698af1f02b84b8a00977e8b2db6cfa0a5d54747e3ac2869874f997c9fceba94f; original global index 8207.
def localCycle00087 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle 6a1756c5b622cf93a7d8907d976cae816ed6186761949278e37c3d597b93fdd8; original global index 8254.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 0, .triangle 14 2, .gapLower 6 2, .triangle 23 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 6acf333a60f4713d289279c176fde67c0e8cc3c850abdd8b6163dfc91cf7a451; original global index 8315.
def localCycle00089 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 4 6, .distance 1 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 23 2, .gapLower 6 1, .gapUpper 4 2]

-- Original cycle 6bb2f54c75747e47550618d680e1ad8369db561d14296b2291fe4ed39522756f; original global index 8381.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 6c52e8b35653e2608f7c5a7067ea69774d1f2198d445956673f994666b89604c; original global index 8439.
def localCycle00091 : Cycle where
  length := 5
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle 6d7d017c8424a549e6205197df1f94112140fa421f32fd2d73d5a3082d725e33; original global index 8510.
def localCycle00092 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 0 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 2, .gapLower 0 2, .triangle 10 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 6edf7b3383c5107c5eee530ea2a84098f2de49c0cd86fe8f97f620a082f595fc; original global index 8601.
def localCycle00093 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![4, -2, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.gapLower 2 6, .gapLower 6 2, .gapLower 6 1, .triangle 18 1, .triangle 17 0, .triangle 26 1, .corridorLower 2 3]

-- Original cycle 7103bd161d2e99f3e49fc24b8bba2f772c4963686f0256fc66bbb433875e701d; original global index 8766.
def localCycle00094 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 72a8c2d617e2e2c0a1195c66e1051727ce3d2eb1feb3f9516111f107cc22c073; original global index 8877.
def localCycle00095 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 755a369ac8c878f382835ec5a86a1d219af3550c9f1d006763442c14550d5879; original global index 9091.
def localCycle00096 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 22 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 7623862f0c91e8d37bac30467b951d8360f2bed9ac0c0d8e0ed21a5f44b56825; original global index 9146.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 30 1, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Original cycle 764e7bdd4cfe4594de6d52f93e2d8ddaddc943905c0439e7258f5f23b362a50b; original global index 9157.
def localCycle00098 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 3]
    constant := ![2, -2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .triangle 14 0, .triangle 10 1]

-- Original cycle 7840523d6c8826a91b10e3f48494c82100cbacbcdb2c7def3221cda4c0196d2c; original global index 9295.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 22 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Original cycle 7863c9a54246b268dee6707020287e5d38e77035b777a6557446042e545d71a1; original global index 9308.
def localCycle00100 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 78c78e7b32a5f0593af93465859abbc1971454cc31e89665adb047530ef7e26f; original global index 9346.
def localCycle00101 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 29 1, .corridorLower 4 6]

-- Original cycle 7abfb0ca7ed80dfd4a11872456bf4e30508b08d9c2933cd3174bcd416bb24b7b; original global index 9500.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 7ac4fc4217f305d13b6eb58bcd6295a60919abf2f98191ffaf1ea17568ce6004; original global index 9503.
def localCycle00103 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 10 1, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 7e288f5d32c0a54ce241fa1715457a1638716314ce592bcab7958d66e0718e90; original global index 9801.
def localCycle00104 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 4 2, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle 7e5d957ad83f3c6f02f128e1b2635929dd11d7d36129e51e1e41c4fc6fffc1b1; original global index 9815.
def localCycle00105 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 0 6, .distance 0 2]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 4, .gapLower 6 3, .triangle 8 1]

-- Original cycle 7ef5525bfc94a070d4a1cc9f7b64370e3dede4a332733216cc5dc023193e9225; original global index 9855.
def localCycle00106 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 4 6, .distance 3 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![4, -2, 0, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.gapLower 4 6, .gapLower 6 4, .triangle 11 2, .gapLower 6 1, .triangle 18 1, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 814650718ecd72222ca710f00d7f32d3777d1c7a2bb6220658129e5b110ef475; original global index 10036.
def localCycle00107 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 10 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 81630eaf319ac2ac47bc2c16e7172f9f883e8c66f619e40ad28639e9ca8f34a1; original global index 10051.
def localCycle00108 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 2 5, .gapLower 4 4, .gapLower 0 4]

-- Original cycle 84cd3e4a0b9185c815da6bc33266c3815d94a7868bcdd61019e3b9120751ee4d; original global index 10311.
def localCycle00109 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -3, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 2, .gapLower 6 2, .triangle 18 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 84cd420d5adc6a0fbaee268bc7c47fb79c2cb5870cceb72f172e491b0f86d697; original global index 10312.
def localCycle00110 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 2, .distance 0 6, .distance 1 6, .distance 2 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -2, 0, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .triangle 6 1, .gapLower 0 3, .triangle 4 1, .triangle 18 1, .triangle 27 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 851dda3dd179a941a05948602653f355511cb365b4c494b5cc9ead8b8d253055; original global index 10330.
def localCycle00111 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 10 1, .triangle 11 0, .triangle 33 1, .triangle 30 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 85d440dda3e33274d8f683db65257288fcdfbf3069a37a3f5ebea0ccb75af89a; original global index 10387.
def localCycle00112 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 30 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 875b069bc28706ed8e8e5922db3ce30857672b8dcee351df13b4e3944c3e65f0; original global index 10497.
def localCycle00113 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 22 0, .triangle 23 0, .corridorLower 4 6]

-- Original cycle 87ef0d373bf60409f15f10e9b7f3d7f8b1de0312a309c71edb3671b30cd2a11d; original global index 10534.
def localCycle00114 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -3, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 8b388e325a4b1366c8e17113bba43fe1c7d5625957a55057ce7fc7ac0ebd7644; original global index 10784.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 8b3d7e26bb0591d10e16447f6d9a54c5597eca9b205cf30b36c7aacfc3c13f35; original global index 10788.
def localCycle00116 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 3 4]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 3 4, .gapUpper 5 5, .gapLower 6 5, .triangle 32 0]

-- Original cycle 8b88213247fbf499985b45637bfede268bb437d2d00a8439fbff80c8b683f37d; original global index 10808.
def localCycle00117 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 28 1, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 8debfabe7c7b8d3d96245a84b40fccd7761d95f7eb2279939268665b675ec5ae; original global index 10988.
def localCycle00118 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 2, 0, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 8e5f537528192d620e0a58215bd0158f52959b1678a924d1ad08271c4063abc3; original global index 11021.
def localCycle00119 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Original cycle 8e8e26f5231900cabb0a59829e30fe7c0ebea3d0563b1fc8d6609d7c4a14236b; original global index 11031.
def localCycle00120 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 9052a3946a0579e242e88252072fd3a0b81968ab29fe0e5ed93adb4060423b1c; original global index 11172.
def localCycle00121 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 0, .triangle 24 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 92d5b7c0978265f5a1ece6fccd713424addd0ecb4da5ccdd2e51872b8a1e792f; original global index 11380.
def localCycle00122 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 30 1, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 94c659b72a58c4a8dc53335ee29010e5be35f9e68691254fcb421cd090a86712; original global index 11546.
def localCycle00123 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -3, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 4 1, .triangle 18 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 95542e32443e10506dc6b8041a6db4c1e2374e3bc6949228a8f9772509681a48; original global index 11603.
def localCycle00124 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -2, 2, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .gapLower 6 6, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 955afde7b114b49c5839e93993535b063bf6f4e77f8a53e19ce22e6127425f65; original global index 11605.
def localCycle00125 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 0, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 9a4812b79d44b7bcb6cbdec1a4bda1f22f8974bd3c8c2dd8786ec892dbe58f3b; original global index 11989.
def localCycle00126 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 9ac751dd71c2da9321be1e02a94a01a3a2f0534765e652ecaa7ec67b2b0a3bf2; original global index 12028.
def localCycle00127 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 2, .gapLower 6 2, .triangle 24 1, .triangle 17 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 9b5bf6f3b94a6e3a0009b77d91f2e4b6e228181e8f7e9a7f03e88b5127626899; original global index 12084.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 28 1, .triangle 22 0, .triangle 23 0, .corridorLower 4 6]

-- Original cycle 9c369386e4ddfa2b399076ae4924f956b243494f76d0072e9382f959fd760df3; original global index 12153.
def localCycle00129 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 24 0, .triangle 17 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 9e675887f14e43bdef9e20e96d3133024cb27825bc49f9390d65941c7949c716; original global index 12334.
def localCycle00130 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 2, .triangle 11 1, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 9e8269f1c95a9c521a339ad678f779d6d7ff8af51076ecf39dff5f9003b36326; original global index 12346.
def localCycle00131 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .theta 1]
    constant := ![3, -1, -2, 3, 0, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapUpper 2 6, .thetaNext 1]

-- Original cycle a2c340432ef79fff514245cef5745820fa3f947ad8c443415f3a8cbaba613260; original global index 12655.
def localCycle00132 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 8 2, .gapLower 6 1, .triangle 23 1, .triangle 16 1, .triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle a2c38ed8617e6e853056b47f789a8b301d733fe8c804fcce0f84dddc0406cd4f; original global index 12656.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle a2d24fe41daccb94a2a047539690d44fb15e5048c0e5c7b29f2725edb014fe4f; original global index 12664.
def localCycle00134 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle a4a6f7fe465cbd063156d8ec0f2422e680cf5d47a6d7d1948ea3f713b2f18383; original global index 12796.
def localCycle00135 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 8 0, .triangle 0 1, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle a4e11ca23b151a210915128123c4b4e2777fc0ba616b76cb4592ad80bff1c3e0; original global index 12814.
def localCycle00136 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 26 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle a50304d8eb6004f94adab0ad004eba8e05a0f8e109d79e6575f88378b1acc926; original global index 12825.
def localCycle00137 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 4, .distance 1 4, .distance 1 2, .distance 2 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .gapLower 4 3, .triangle 16 1, .triangle 18 0, .triangle 30 1, .triangle 26 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle a668c740521f5f46d224af38c56fd91e02e43e62f4a230a5e104e55b8df8ab8e; original global index 12929.
def localCycle00138 : Cycle where
  length := 16
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, 3, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle a9707215f99a8e69d5fcd6ef958d61def534f35a301e1e20c240afc21aadd29c; original global index 13190.
def localCycle00139 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 3 6, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 33 1]

-- Original cycle aec44c21233c49725093d48389517b1aa49bc46bb034b1c80ebd0bb858070e2f; original global index 13641.
def localCycle00140 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapLower 6 2, .triangle 13 1, .triangle 6 1, .corridorLower 0 2, .thetaLower 0]

-- Original cycle af0d6e9717ad64d30d3c037f28f7017d827030706c2e7ec10522896a9d2196ca; original global index 13666.
def localCycle00141 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .gapLower 6 2, .triangle 4 1, .gapLower 6 0]

-- Original cycle af2d60e7843e13219b3abdf796f98098929fcb0256d227626dc6cde626a49c24; original global index 13681.
def localCycle00142 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 8 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle b0af52f1f5a9104baef62822e85c2d2ddb51fde0b32ca4fcf298f8b59cd5c978; original global index 13795.
def localCycle00143 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -3, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .gapLower 6 2, .triangle 4 1, .triangle 18 1, .triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b2a00cf25d025e2b3e4b6b9c8c92f3862e1c3f8436b63c49b245d4fa0600a6df; original global index 13961.
def localCycle00144 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle b42483da2939150866d7c220eaaae973e2f6bc0dbf6d3417736726eee6738b0c; original global index 14067.
def localCycle00145 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 10 1, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle b42bc4d2c6a84de0d3ed2f749a61aba022f1ad576b3fc65c66eb0f3a5c72f585; original global index 14071.
def localCycle00146 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Original cycle b59db8affabd8fb479f1fd5ef59c2af61c34c984aa813877db0f30811bded964; original global index 14190.
def localCycle00147 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 2 1, .triangle 16 1, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle ba24c73c7f2e76525993f51339c671d8e0e32eb115e9ef7baca406b85d41ac32; original global index 14535.
def localCycle00148 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 26 1, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle bac9013c71f598ffead646dddf1df16113f43d6b73d862bb19f05c395a93098b; original global index 14589.
def localCycle00149 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 0 5, .distance 1 5, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .gapLower 0 3, .gapLower 0 2, .gapLower 5 3, .triangle 17 1, .triangle 28 1, .corridorLower 4 5]

-- Original cycle bb62f04c6725b6bcaddb4244b52f7d5426b944f373b1c921b875da631ac82016; original global index 14630.
def localCycle00150 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 22 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Original cycle bf119a2c9f50863aa98e4e1c22a0e0d8402cedece004aec7dfe9511f370f6580; original global index 14906.
def localCycle00151 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 30 1, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle bf79df876bfc55c1fcceb0549c0c7cd9ac22cceb8bdba7f6833840e1cb628e02; original global index 14941.
def localCycle00152 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 29 1, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Original cycle c001d7055cd3870c9bbb5e72194f3bc03c3a0b7633d9b8d6e5b1cf125987adc9; original global index 14988.
def localCycle00153 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 3, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle c2cf3177a1cabf8ceb906ca253abc56db320e564398c9f891d87c4f0ba37531a; original global index 15202.
def localCycle00154 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Original cycle c3c9e23fceca955a6b3558089ed3651df183ef27a516fba669f12c0c976da477; original global index 15275.
def localCycle00155 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Original cycle c400d9b454303d293796cbaf806948f99ee9512418a532d27b147809dc6a793f; original global index 15288.
def localCycle00156 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .gapLower 3 0]

-- Original cycle c4095b7bcfac7ea967634d9167cf62f7dfdad639b8a704755c6634a3efabbf79; original global index 15291.
def localCycle00157 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 2, .gapLower 6 1, .triangle 18 1, .triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle c4285a40ed51fb7b9a2fb91dd1413275a8f7df7acdc5093408978b53199ad159; original global index 15303.
def localCycle00158 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 1 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -3, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .gapLower 0 3, .triangle 4 1, .triangle 18 1, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle c49cdef1cf96a1fb331e1f6ed3ea887b4bc77c5328bac4976ccf8065b9332b6e; original global index 15332.
def localCycle00159 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 22 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle c50125fc3ec120e0d023db08730ae83d8e980630d645ccc01d06e0ee7a7a492d; original global index 15371.
def localCycle00160 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 17 2, .triangle 24 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle c5e519dd14286e80d3047b644917bab3fe5449ed059f7f3196cd05984ad933fd; original global index 15432.
def localCycle00161 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .theta 1]
    constant := ![3, -1, -1, -2, 2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .gapLower 6 0, .gapLower 6 6, .triangle 33 0, .triangle 20 0, .corridorLower 1 3]

-- Original cycle c6235fa49366f7e0094677b005840e51f1770e0e1994adeb5e1a83b48a84ac98; original global index 15454.
def localCycle00162 : Cycle where
  length := 15
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 0 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle c65e10a55a56eb719728fe1c0f36de1191e9df5d99e3d382cdbb244f51312b2a; original global index 15473.
def localCycle00163 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 6 1, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c6ff5acac1c3023af1c188dc1997604fdc5951c109af9d31973aaa3564957e60; original global index 15528.
def localCycle00164 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![4, -2, 0, -2, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false] }
  origin := ![.gapLower 4 6, .gapLower 6 4, .triangle 27 2, .gapLower 6 2, .triangle 4 1, .triangle 18 1, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle c77d3737e805f7596261c1a7d9239bac9960894242517bd005b7e9c3ea98f2cf; original global index 15567.
def localCycle00165 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .triangle 14 0, .triangle 7 1]

-- Original cycle c93faffd79901995e57e10bc58d70eecf597c9693bf76f09d16667d6ba95198e; original global index 15731.
def localCycle00166 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle cbb0cad424ed2e2f5d4709be9f984a3e4e6ac5915355fc927295fbf5bac96841; original global index 15913.
def localCycle00167 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 26 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle cd8bf326c00a221ce4728825695dfc1e8370a9bee5b560129c9fff891ebefe08; original global index 16064.
def localCycle00168 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 5, .distance 0 3]
    constant := ![2, 0, -2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 3 3, .triangle 11 2, .gapLower 0 2, .gapLower 0 1]

-- Original cycle cfb8e2544ec97e0ea43942dc5b696a695f44cd3a6e3cb7e4954e763be5d23a97; original global index 16211.
def localCycle00169 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 3 6, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 5, .gapLower 6 4, .triangle 32 1]

-- Original cycle d158b39bde4b5a30be7918012ca0cc842ba5fd4faf99b8956f651ab3a51c006b; original global index 16342.
def localCycle00170 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle d222da60c63da2cd7eca4fb7a09c4ecaf7ce64dd4f824aae6d507386d5723d10; original global index 16397.
def localCycle00171 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 0 6, .distance 0 2]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .gapLower 6 3, .triangle 8 1]

-- Original cycle d6a8b2f2c0291a720414d76c20da066ea9176e32047bb9eec3dccc8588fcabb9; original global index 16755.
def localCycle00172 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 14 2, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle d90c1b65969b5333abf9353b6f826d9819bb79e38fe1eb4444ae0170c5e4843d; original global index 16954.
def localCycle00173 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -1, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle db2e9feb633fd0c79946a6e23d54802743d3c4d2e75d4a0d3cb3bc40500f94d5; original global index 17129.
def localCycle00174 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 4 6, .theta 4, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 21 2, .gapLower 6 1, .corridorLower 4 6, .thetaLower 4]

-- Original cycle e32d008b72a6f9cd43a2a393f24a99ea83fbfa90976d902015ed7c573887e132; original global index 17770.
def localCycle00175 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 24 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle e3ddc4456b2b47731774931c5a6a258e2df75a3e3cd8e891c413ac0d97dfcb86; original global index 17827.
def localCycle00176 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .triangle 30 1, .triangle 24 0, .triangle 17 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle e552319c1dcd7a01665ec4aab6697ee729802969074f6a83029ddfaa9af7d0d9; original global index 17928.
def localCycle00177 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -3, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle e587a24b80c5221b4f1458074afb4746719cadd7c933731992032a61c0f1e570; original global index 17953.
def localCycle00178 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 0 2]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 5 2, .gapUpper 3 3, .gapLower 6 5, .triangle 8 0]

-- Original cycle e6ce55a68194da13141588c6f4b53bdc60be0871ce07567a2edd72d59ff7a29e; original global index 18057.
def localCycle00179 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 3]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 3 3, .triangle 33 1, .triangle 14 0, .gapLower 0 1]

-- Original cycle e89660aaba06ccd6f9b92703836c779fddc245f0edca7423c01c36272bc7b349; original global index 18180.
def localCycle00180 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 2, .distance 0 6, .distance 0 5, .distance 1 5, .theta 1]
    constant := ![3, -2, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .triangle 6 1, .triangle 8 2, .gapLower 0 2, .gapLower 5 3, .corridorLower 1 5]

-- Original cycle ec50698efe9367b26bd0370141de9a9ba5d9d60786805b9e77fd1f93d29fce50; original global index 18443.
def localCycle00181 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 18 0, .triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ed809953c55a2e2bc2f7d322c6d32257743932c16f6b8bca53b113a71c010a19; original global index 18541.
def localCycle00182 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 0 5, .distance 1 5, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 2, .gapLower 0 2, .triangle 3 1, .triangle 17 1, .triangle 28 1, .corridorLower 4 5]

-- Original cycle ef22881884715b3698552465e8b584d55049121359be9ae300079fd7b7ef2664; original global index 18658.
def localCycle00183 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle f25c7153b116f2cb1b7a60a997a1cabf178363968f838cfbee8c03304d09b0f4; original global index 18900.
def localCycle00184 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 2 1, .gapUpper 1 5]

-- Original cycle f542610fe57ef15ad08179af166667c3c69fd5801340561a977b2a91ee064a92; original global index 19117.
def localCycle00185 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle f9707dfa269329d6eb8888be3deb5ea431d16af445eabe5df1235f2f38e5bfa9; original global index 19449.
def localCycle00186 : Cycle where
  length := 15
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 8 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle fac3cbf2025ca64179b91d4a527e0f9117cb6cb1503b3d6d07310e8853e0b7c9; original global index 19564.
def localCycle00187 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 4 1, .triangle 18 1, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle fc13bfc353811fb20032440ce9ee8a3f45b2e28a193a8ecd06893890e5b300ea; original global index 19682.
def localCycle00188 : Cycle where
  length := 4
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .theta 5, .zero]
    constant := ![0, 1, -2, 0]
    coefficient := ![1, 1, -1, 0]
    strict := ![false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapUpper 5 6, .thetaLower 5]

-- Original cycle fc87cd854bc4e902e736c4dee4f6a2d2a8f8bfd1186b9ce592519007298314f1; original global index 19728.
def localCycle00189 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 4, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 2, .triangle 13 2, .gapLower 6 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle ff72d0e06c7d596387f98b8967dcd96a17d845cfd357e27f40cd51a4a11f51a2; original global index 19972.
def localCycle00190 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .theta 6, .zero]
    constant := ![0, 3, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 1, .corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .gapLower 6 0, .thetaLower 6]

def library : Library := fun id => if id < 95 then (if id < 47 then (if id < 23 then (if id < 11 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 8 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none))) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none))))) else (if id < 17 then (if id < 14 then (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none))) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)))) else (if id < 20 then (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none))) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)))))) else (if id < 35 then (if id < 29 then (if id < 26 then (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none))) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none)))) else (if id < 32 then (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none))) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none))))) else (if id < 41 then (if id < 38 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none))) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)))) else (if id < 44 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none))) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none))))))) else (if id < 71 then (if id < 59 then (if id < 53 then (if id < 50 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none))) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)))) else (if id < 56 then (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none))) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none))))) else (if id < 65 then (if id < 62 then (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none))) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)))) else (if id < 68 then (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none))) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)))))) else (if id < 83 then (if id < 77 then (if id < 74 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none))) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)))) else (if id < 80 then (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none))) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none))))) else (if id < 89 then (if id < 86 then (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none))) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)))) else (if id < 92 then (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none))) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)))))))) else (if id < 143 then (if id < 119 then (if id < 107 then (if id < 101 then (if id < 98 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none))) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)))) else (if id < 104 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none))) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none))))) else (if id < 113 then (if id < 110 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none))) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none)))) else (if id < 116 then (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none))) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none)))))) else (if id < 131 then (if id < 125 then (if id < 122 then (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none))) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)))) else (if id < 128 then (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none))) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none))))) else (if id < 137 then (if id < 134 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none))) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)))) else (if id < 140 then (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none))) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none))))))) else (if id < 167 then (if id < 155 then (if id < 149 then (if id < 146 then (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none))) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none)))) else (if id < 152 then (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none))) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none))))) else (if id < 161 then (if id < 158 then (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none))) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none)))) else (if id < 164 then (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none))) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none)))))) else (if id < 179 then (if id < 173 then (if id < 170 then (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none))) else (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none)))) else (if id < 176 then (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id = 175 then some localCycle00175 else none))) else (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id = 178 then some localCycle00178 else none))))) else (if id < 185 then (if id < 182 then (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none))) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none)))) else (if id < 188 then (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id = 187 then some localCycle00187 else none))) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![3, 2, 5, 6, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 0, 2, 3, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 42 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20736)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![3, 2, 5, 6, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 0, 2, 6, 3], ![1, 4, 0, 2, 5, 3]], proof := .tail 162 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20737)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![3, 2, 5, 6, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 0, 6, 2, 3], ![1, 4, 0, 5, 2, 3]], proof := .tail 154 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20738)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![3, 2, 6, 5, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 0, 2, 3], ![1, 4, 5, 0, 2, 3]], proof := .tail 129 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20739)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![3, 2, 5, 6, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 0, 2, 3, 6], ![4, 1, 0, 2, 3, 5]], proof := .low6 (![190, 89, 109, 123, 81, 139, 31, 18, 43, 17, 87, 91, 32, 27, 120, 40, 174, 15, 126, 170, 69, 127, 47, 1, 82, 52, 49, 2]) }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20740)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![3, 2, 5, 6, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 0, 2, 6, 3], ![4, 1, 0, 2, 5, 3]], proof := .tail 64 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20741)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![3, 2, 5, 6, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 0, 6, 2, 3], ![4, 1, 0, 5, 2, 3]], proof := .low6 (![54, 89, 172, 28, 83, 12, 176, 121, 88, 125, 165, 178, 48, 189, 173, 165, 178, 5, 153, 165, 178, 29, 171, 0, 75, 98, 165, 178]) }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20742)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![3, 2, 6, 5, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 0, 2, 3], ![4, 1, 5, 0, 2, 3]], proof := .tail 129 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20743)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![3, 2, 6, 5, 4, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 1, 0, 2, 3]], proof := .tail 150 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20744)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![3, 2, 6, 5, 4, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 1, 0, 2, 3]], proof := .tail 99 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20745)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![3, 6, 2, 5, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 0, 2, 3], ![1, 4, 5, 2, 0, 3]], proof := .tail 97 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20746)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![3, 6, 2, 5, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 0, 2, 3], ![4, 1, 5, 2, 0, 3]], proof := .tail 134 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20747)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![3, 6, 2, 5, 4, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 1, 2, 0, 3]], proof := .tail 96 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20748)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![3, 6, 2, 5, 4, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 41 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20749)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![3, 6, 2, 5, 4, 1], ![3, 6, 2, 5, 4, 0], ![3, 6, 1, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 2, 1, 0, 3]], proof := .tail 134 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20750)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![3, 6, 2, 5, 4, 1], ![3, 6, 2, 5, 4, 0], ![3, 6, 1, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 99 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20751)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 0, 2, 3], ![1, 4, 5, 2, 3, 0]], proof := .tail 146 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20752)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 0, 2, 3], ![4, 1, 5, 2, 3, 0]], proof := .tail 61 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20753)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 1, 2, 3, 0]], proof := .tail 159 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20754)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![3, 6, 2, 5, 4, 0], ![3, 6, 1, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 2, 1, 3, 0]], proof := .tail 175 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20755)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![6, 3, 2, 5, 4, 0], ![3, 6, 1, 0, 5, 4], ![2, 6, 1, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 2, 3, 1, 0]], proof := .tail 61 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20756)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 71 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20757)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![3, 6, 2, 5, 4, 0], ![3, 6, 1, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 22 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20758)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![6, 3, 2, 5, 4, 0], ![3, 6, 1, 0, 5, 4], ![2, 6, 1, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 24 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20759)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![6, 3, 2, 5, 4, 0], ![6, 3, 1, 0, 5, 4], ![6, 2, 1, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 3, 2, 1, 0]], proof := .tail 37 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20760)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![6, 3, 2, 5, 4, 0], ![6, 3, 1, 0, 5, 4], ![6, 2, 1, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 6 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20761)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 0, 4, 6], ![2, 1, 0, 5, 4, 6], ![1, 5, 0, 2, 3, 6], ![1, 4, 2, 0, 3, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 84 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20762)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 0, 4, 6], ![2, 1, 0, 5, 6, 4], ![1, 5, 0, 2, 6, 3], ![1, 4, 2, 0, 3, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 8 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20763)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 5, 6, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 2, 0, 3, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 163 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20764)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![3, 5, 2, 6, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 5, 6, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 0, 3, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 86 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20765)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 0, 4, 6], ![2, 1, 0, 6, 5, 4], ![1, 5, 0, 2, 6, 3], ![1, 4, 2, 0, 6, 3], ![1, 0, 2, 4, 5, 3]], proof := .tail 65 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20766)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 6, 5, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 2, 0, 6, 3], ![1, 0, 4, 2, 5, 3]], proof := .tail 21 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20767)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![3, 5, 2, 6, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 6, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 0, 6, 3], ![1, 4, 0, 2, 5, 3]], proof := .tail 183 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20768)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 0, 5, 6, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 0, 3, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 151 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20769)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 0, 6, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 0, 6, 3], ![1, 4, 2, 0, 5, 3]], proof := .tail 151 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20770)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 0, 6, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 6, 0, 3], ![1, 4, 2, 5, 0, 3]], proof := .tail 112 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20771)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 6, 2, 0, 3], ![1, 4, 5, 2, 0, 3]], proof := .tail 11 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20772)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![1, 6, 5, 0, 2, 3], ![1, 6, 4, 2, 0, 3], ![1, 5, 4, 2, 0, 3]], proof := .tail 16 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20773)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![1, 6, 5, 0, 2, 3], ![6, 1, 4, 2, 0, 3], ![5, 1, 4, 2, 0, 3]], proof := .tail 94 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20774)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 2, 0, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 113 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20775)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 2, 0, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 44 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20776)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 6, 0, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 6, 0, 3], ![1, 4, 2, 5, 3, 0]], proof := .tail 51 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20777)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 6, 2, 0, 3], ![1, 4, 5, 2, 3, 0]], proof := .tail 11 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20778)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![1, 6, 5, 0, 2, 3], ![1, 6, 4, 2, 0, 3], ![1, 5, 4, 2, 3, 0]], proof := .tail 16 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20779)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![1, 6, 5, 0, 2, 3], ![6, 1, 4, 2, 0, 3], ![5, 1, 4, 2, 3, 0]], proof := .tail 94 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20780)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 2, 0, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 113 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20781)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 2, 0, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 44 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20782)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![6, 3, 2, 4, 5, 0], ![3, 6, 1, 5, 0, 4], ![2, 6, 1, 0, 5, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 2, 0, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 44 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20783)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![6, 3, 2, 4, 5, 0], ![6, 3, 1, 5, 0, 4], ![6, 2, 1, 0, 5, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 2, 0, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 133 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20784)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 0, 4, 6], ![2, 1, 0, 5, 4, 6], ![5, 1, 0, 2, 3, 6], ![4, 1, 2, 0, 3, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 84 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20785)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 0, 4, 6], ![2, 1, 0, 5, 6, 4], ![5, 1, 0, 2, 6, 3], ![4, 1, 2, 0, 3, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 8 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20786)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 2, 0, 3, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 163 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20787)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![3, 5, 2, 6, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 0, 3, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 186 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20788)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![3, 5, 2, 6, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 0, 3, 6], ![4, 1, 0, 2, 3, 5]], proof := .tail 142 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20789)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 0, 4, 6], ![2, 1, 0, 6, 5, 4], ![5, 1, 0, 2, 6, 3], ![4, 1, 2, 0, 6, 3], ![1, 0, 2, 4, 5, 3]], proof := .tail 65 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20790)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 2, 0, 6, 3], ![1, 0, 4, 2, 5, 3]], proof := .tail 21 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20791)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![3, 5, 2, 6, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 0, 6, 3], ![1, 4, 0, 2, 5, 3]], proof := .tail 138 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20792)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![3, 5, 2, 6, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 0, 6, 3], ![4, 1, 0, 2, 5, 3]], proof := .tail 4 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20793)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 0, 5, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 0, 3, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 152 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20794)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 0, 6, 3], ![1, 4, 2, 0, 5, 3]], proof := .tail 152 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20795)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 6, 0, 3], ![1, 4, 2, 5, 0, 3]], proof := .tail 155 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20796)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 2, 0, 3], ![1, 4, 5, 2, 0, 3]], proof := .tail 11 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20797)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 0, 5, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 0, 3, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 122 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20798)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 0, 6, 3], ![4, 1, 2, 0, 5, 3]], proof := .tail 122 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20799)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 6, 0, 3], ![4, 1, 2, 5, 0, 3]], proof := .tail 112 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20800)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 2, 0, 3], ![4, 1, 5, 2, 0, 3]], proof := .tail 11 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20801)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 1, 2, 0, 3]], proof := .tail 102 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20802)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 94 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20803)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 6, 2, 5, 4, 0], ![3, 6, 1, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 2, 1, 0, 3]], proof := .tail 70 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20804)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 6, 2, 5, 4, 0], ![3, 6, 1, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 44 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20805)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 6, 0, 3], ![1, 4, 2, 5, 3, 0]], proof := .tail 73 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20806)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 2, 0, 3], ![1, 4, 5, 2, 3, 0]], proof := .tail 11 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20807)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 6, 0, 3], ![4, 1, 2, 5, 3, 0]], proof := .tail 111 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20808)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 2, 0, 3], ![4, 1, 5, 2, 3, 0]], proof := .tail 11 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20809)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 1, 2, 3, 0]], proof := .tail 102 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20810)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 94 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20811)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 6, 2, 5, 4, 0], ![3, 6, 1, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 2, 1, 3, 0]], proof := .tail 70 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20812)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 6, 2, 5, 4, 0], ![3, 6, 1, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 44 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20813)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![6, 3, 2, 5, 4, 0], ![3, 6, 1, 5, 0, 4], ![2, 6, 1, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 2, 3, 1, 0]], proof := .tail 70 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20814)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![6, 3, 2, 5, 4, 0], ![3, 6, 1, 5, 0, 4], ![2, 6, 1, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 44 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20815)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![6, 3, 2, 5, 4, 0], ![6, 3, 1, 5, 0, 4], ![6, 2, 1, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 3, 2, 1, 0]], proof := .tail 119 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20816)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![6, 3, 2, 5, 4, 0], ![6, 3, 1, 5, 0, 4], ![6, 2, 1, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 133 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20817)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 0, 4, 6], ![2, 1, 0, 5, 4, 6], ![5, 1, 0, 2, 3, 6], ![4, 2, 1, 0, 3, 6], ![1, 0, 2, 3, 4, 5]], proof := .low6 (![45, 104, 143, 114, 169, 13, 167, 59, 141, 131, 50, 116, 124, 93, 132, 106, 116, 157, 140, 164, 116, 53, 26, 116, 118, 34, 56, 116]) }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20818)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 0, 4, 6], ![2, 1, 0, 5, 6, 4], ![5, 1, 0, 2, 6, 3], ![4, 2, 1, 0, 3, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 30 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20819)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 0, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 2, 1, 0, 3, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 62 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20820)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![3, 5, 2, 6, 4, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 0, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 1, 0, 3, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 33 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20821)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![3, 5, 2, 6, 4, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 0, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 0, 3, 6], ![4, 1, 0, 2, 3, 5]], proof := .low6 (![190, 89, 76, 105, 177, 139, 188, 18, 43, 17, 23, 91, 161, 27, 120, 40, 174, 58, 74, 39, 69, 19, 79, 1, 187, 181, 23, 80]) }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20822)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 0, 4, 6], ![2, 1, 0, 6, 5, 4], ![5, 1, 0, 2, 6, 3], ![4, 2, 1, 0, 6, 3], ![1, 0, 2, 4, 5, 3]], proof := .tail 115 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20823)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 0, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 0, 6, 2, 3], ![4, 2, 1, 0, 6, 3], ![1, 0, 4, 2, 5, 3]], proof := .tail 147 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20824)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![3, 5, 2, 6, 4, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 0, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 1, 0, 6, 3], ![1, 4, 0, 2, 5, 3]], proof := .tail 57 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20825)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![3, 5, 2, 6, 4, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 0, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 0, 6, 3], ![4, 1, 0, 2, 5, 3]], proof := .tail 135 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20826)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 0, 5, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 1, 0, 3, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 95 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20827)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 1, 0, 6, 3], ![1, 4, 2, 0, 5, 3]], proof := .tail 95 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20828)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 1, 6, 0, 3], ![1, 4, 2, 5, 0, 3]], proof := .tail 144 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20829)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 0, 5, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 0, 3, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 95 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20830)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 0, 6, 3], ![4, 1, 2, 0, 5, 3]], proof := .tail 95 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20831)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 6, 0, 3], ![4, 1, 2, 5, 0, 3]], proof := .tail 144 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20832)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![3, 5, 6, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 1, 0, 5, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 0, 3, 6], ![4, 2, 1, 0, 3, 5]], proof := .low0 (![107, 38, 182, 158, 108, 35, 46, 7, 92, 20, 85, 184, 60, 63, 7, 7, 7, 7, 149, 85, 180, 3, 85, 110, 3, 67, 85, 137]) }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20833)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![3, 5, 6, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 0, 6, 3], ![4, 2, 1, 0, 5, 3]], proof := .low0 (![25, 77, 72, 158, 108, 35, 46, 179, 92, 20, 85, 184, 3, 168, 179, 85, 179, 179, 149, 85, 180, 3, 85, 110, 3, 67, 85, 137]) }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20834)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 5, 6, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 6, 0, 3], ![4, 2, 1, 5, 0, 3]], proof := .tail 185 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20835)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 6, 5, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 6, 1, 0, 3], ![4, 2, 5, 1, 0, 3]], proof := .tail 160 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20836)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 6, 5, 2, 4, 0], ![3, 6, 5, 1, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 2, 1, 0, 3], ![4, 5, 2, 1, 0, 3]], proof := .tail 11 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20837)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 6, 5, 2, 4, 0], ![3, 6, 5, 1, 0, 4], ![2, 1, 0, 6, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 2, 1, 0, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 90 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20838)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 1, 6, 0, 3], ![1, 4, 2, 5, 3, 0]], proof := .tail 145 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20839)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 6, 0, 3], ![4, 1, 2, 5, 3, 0]], proof := .tail 145 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20840)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 5, 6, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 6, 0, 3], ![4, 2, 1, 5, 3, 0]], proof := .tail 103 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20841)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 6, 5, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 6, 1, 0, 3], ![4, 2, 5, 1, 3, 0]], proof := .tail 66 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20842)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 6, 5, 2, 4, 0], ![3, 6, 5, 1, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 2, 1, 0, 3], ![4, 5, 2, 1, 3, 0]], proof := .tail 11 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20843)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 6, 5, 2, 4, 0], ![3, 6, 5, 1, 0, 4], ![2, 1, 6, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 2, 1, 0, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 9 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20844)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![6, 3, 5, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 6, 1, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 6, 1, 0, 3], ![4, 2, 5, 3, 1, 0]], proof := .tail 14 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20845)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![6, 3, 5, 2, 4, 0], ![3, 6, 5, 1, 0, 4], ![2, 6, 1, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 2, 1, 0, 3], ![4, 5, 2, 3, 1, 0]], proof := .tail 11 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20846)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![6, 3, 5, 2, 4, 0], ![3, 6, 5, 1, 0, 4], ![2, 6, 1, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 2, 1, 0, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 14 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20847)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![6, 3, 5, 2, 4, 0], ![6, 3, 5, 1, 0, 4], ![6, 2, 1, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 2, 1, 0, 3], ![4, 5, 3, 2, 1, 0]], proof := .tail 148 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20848)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![6, 3, 5, 2, 4, 0], ![6, 3, 5, 1, 0, 4], ![6, 2, 1, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 2, 1, 0, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 136 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20849)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 0, 4, 6], ![2, 1, 5, 0, 4, 6], ![1, 5, 0, 2, 3, 6], ![1, 4, 2, 3, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 10 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20850)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 0, 4, 6], ![2, 1, 5, 0, 6, 4], ![1, 5, 0, 2, 6, 3], ![1, 4, 2, 3, 0, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 156 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20851)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 5, 0, 6, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 2, 3, 0, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 100 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20852)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 5, 0, 6, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 3, 0, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 36 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20853)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 5, 0, 6, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 3, 0, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 130 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20854)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 5, 6, 0, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 3, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 166 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20855)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 5, 6, 0, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 3, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 112 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20856)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 6, 5, 0, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 6, 3, 0], ![1, 4, 2, 5, 3, 0]], proof := .tail 68 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20857)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 6, 2, 3, 0], ![1, 4, 5, 2, 3, 0]], proof := .tail 78 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20858)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![1, 6, 5, 0, 2, 3], ![1, 6, 4, 2, 3, 0], ![1, 5, 4, 2, 3, 0]], proof := .tail 117 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20859)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![1, 6, 5, 0, 2, 3], ![6, 1, 4, 2, 3, 0], ![5, 1, 4, 2, 3, 0]], proof := .tail 36 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20860)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 2, 3, 0], ![5, 4, 1, 2, 3, 0]], proof := .tail 128 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20861)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 2, 3, 0], ![5, 4, 2, 1, 3, 0]], proof := .tail 101 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20862)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 3, 2, 4, 5, 0], ![3, 6, 1, 5, 0, 4], ![2, 6, 1, 5, 0, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 2, 3, 0], ![5, 4, 2, 3, 1, 0]], proof := .tail 55 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20863)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (20736 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 20736 ≤ id.val) (hhigh : id.val < 20864) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 20736)) = true := by
  let j : Fin 128 := ⟨id.val - 20736, by omega⟩
  have hsum : 20736 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (20736 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard162
