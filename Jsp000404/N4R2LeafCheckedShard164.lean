import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard164
open N4R2RowDataReplay

-- Original cycle 008279f983590a09b152e0898dfa6c8248d38244c390d7b3338662cce842e69e; original global index 47.
def localCycle00000 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 0 1, .triangle 16 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 02cc5d901d74df51c7e06ebdf1b6a535c6ac2fcd06894bd95b98aeafe4806712; original global index 219.
def localCycle00001 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 2 5, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![4, -1, -2, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 7 0, .gapLower 0 3, .triangle 13 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 03a5ebce345296efb83463c2ae3a724c3f74a044994f23047e76743180df2077; original global index 297.
def localCycle00002 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 03cc8ebd8e6e21e6e97240346f7c71bc53aa2f8f576eeec999d75d5bfb531f71; original global index 307.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 5, .distance 0 2, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .theta 0]
    constant := ![2, 0, 0, -2, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.gapLower 0 6, .triangle 3 2, .triangle 7 1, .gapLower 0 3, .triangle 13 0, .triangle 23 0, .gapLower 1 1, .corridorLower 1 3, .thetaNext 0]

-- Original cycle 061dfbd8e51f32209bf2880a858cc1d1a26ef13d6b5ceb09b63afbc2fa9e6c54; original global index 505.
def localCycle00004 : Cycle where
  length := 3
  data := {
    node := ![.theta 0, .distance 0 1, .theta 1, .theta 0]
    constant := ![2, -2, 0]
    coefficient := ![1, -1, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 6, .gapUpper 1 6, .thetaNext 0]

-- Original cycle 06dcb68afbce06992f7cde0c2d26d5c97f82d3a6f172dd0f7719ee448b86fbec; original global index 566.
def localCycle00005 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 0b3943b63bdd84adf2531174d354404678ae0f891c1f388b9ae0015071ef84f2; original global index 898.
def localCycle00006 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 3 6, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 32 1]

-- Original cycle 0cbb271bb16458b51865e5d40c2191a8ff7c9dbc94375e6e55323ed5ad3efc5f; original global index 1008.
def localCycle00007 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 5 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -2, -2, 0, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Original cycle 0cfd0fbe4ce38c75ff60c9e1f6ed105c37377548f759c38580006736c912ac16; original global index 1027.
def localCycle00008 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 0, .triangle 31 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 0d0f46bfa95409c1728b9f644ef2d801330908667d048ca0f620f3cc9602df8d; original global index 1033.
def localCycle00009 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 0f89f348bd087bc68c4e081cc8e3722c7cc3e34f5fcbdde2cc331754ac20346e; original global index 1239.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -1, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 4 0, .triangle 24 1, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 10d26cb1c0cf682c48c43a728266bb48319f5166af80185bd29ba246ff3d2f30; original global index 1347.
def localCycle00011 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 11 2, .gapLower 6 1, .triangle 24 1, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 11da1eb307dd89bea0b817f8c16f17d717fa4286d7b159970e2b17ba4c54d771; original global index 1426.
def localCycle00012 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 1283a4054a5cc4818759a7eee2844204a1ed19454eff015c86f22007d55a7dbb; original global index 1468.
def localCycle00013 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .gapUpper 2 6, .thetaNext 1, .thetaLower 1]

-- Original cycle 12db5f5ae041a0a2d7fd91723eb6c102be1b26a654669dcc2e413d029094a5ad; original global index 1485.
def localCycle00014 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 0 6, .distance 1 6, .distance 2 6, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -2, 0, -2, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, true, false, true] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .triangle 7 1, .gapLower 0 3, .triangle 4 1, .triangle 18 1, .triangle 29 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 13c259e1b5af366584a17983dfdce998b4a1aa7c6b1b45a47ba7181943293a90; original global index 1565.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 2, .gapLower 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 141a0d51303a361c62612c38fa8615dcc1b47f01dcf4fb0f339694c26431c50c; original global index 1587.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 15b3a747d0d0be85ff1079afcd545fafc1caa946b09b2c385f11a1a0a609daef; original global index 1725.
def localCycle00017 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 4 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 32 1, .gapLower 6 3, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 17302907173a939d41b32ea4cd36533bc078a8514172c965cc4260adfddbedaa; original global index 1823.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .gapLower 0 2, .triangle 9 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 177a2f705819c3079d5ac1791fbf76e686559dd49de7ce2fda31ba890b74d7e7; original global index 1838.
def localCycle00019 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 18c38bb5f7f65c5c6a313f64f926a35632a3ee2c2cf9c550f6fbce3044fbddc2; original global index 1936.
def localCycle00020 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .theta 2, .theta 1]
    constant := ![3, -1, -2, 3, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, -1, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .corridorUpper 5 6, .gapLower 6 5, .triangle 29 2, .gapUpper 2 6, .thetaNext 1]

-- Original cycle 1b5fd094aaae08b2a050d951057989bd6f58fae1785ba08f4567f64aa1e0a638; original global index 2121.
def localCycle00021 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 13 0, .triangle 9 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 1eb9cb23861fa619bfb0292c87ef1283b617f03d30322b4596bb7fa5e68b5c6e; original global index 2358.
def localCycle00022 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 29 2, .gapLower 6 2, .triangle 4 1, .triangle 18 1, .triangle 16 0, .gapLower 4 0]

-- Original cycle 1f35ddb562819c41d5c95585151c31e2275f966544f77b917d03611517577f1a; original global index 2395.
def localCycle00023 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 1f3b3927ecae777f355251b21dacb572f3afac9b0dbd1e639049d623c32d7e95; original global index 2399.
def localCycle00024 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .gapLower 0 3, .triangle 13 1, .triangle 9 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 1f63cf7795347fa9e40a660e1c2f19f77ddfa67d606062435cdefcaebf839dba; original global index 2408.
def localCycle00025 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 16 2, .triangle 23 0, .corridorLower 4 6]

-- Original cycle 229247cc829ac4523b37ebae8f92aa3342a4b8c2d43cb33cbfe2cd44829a0a3b; original global index 2644.
def localCycle00026 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 0 2]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 6 2, .gapUpper 4 3, .gapLower 6 4, .triangle 8 0]

-- Original cycle 22d8be4aaa02611194458d743a60a2853b42f7098370163c924d0eb626060ea7; original global index 2667.
def localCycle00027 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 4 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 29 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 22dcf08443cccfe2bc2cc4faa998600548f1dea5b4fe1cd1abdb667d06645b9c; original global index 2671.
def localCycle00028 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 2 6, .distance 0 6, .distance 0 4]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 3, .gapLower 6 4, .gapLower 6 3, .triangle 13 1]

-- Original cycle 233b14d22a36385ec351c41710eb01d85cdda609964fb5fbb0817ba8504ca2f9; original global index 2702.
def localCycle00029 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -3, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .gapLower 6 2, .triangle 4 1, .triangle 18 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 23adc8a42ebc71a1ed3573de38f70a030c27f6c8d5f85b5442f6f6bc9a9a0977; original global index 2736.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 1 3, .theta 1]
    constant := ![3, -1, -2, 2, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .gapLower 6 6, .triangle 34 0, .triangle 31 0, .triangle 19 0, .corridorLower 1 3]

-- Original cycle 251e0ca10ff9d9bf07708a17453c90398ae04127b4fc3d6c1a12f9b1221254bb; original global index 2853.
def localCycle00031 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 0 4, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 13 0, .triangle 6 1, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 254843a0483a069d6c731afc599563a7e90c74764f6091dcdbfe23e8ee37e1a3; original global index 2866.
def localCycle00032 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 25cb1f96242aa582ac340927f50c801c160a602be56cc9c3411a3267f77e198d; original global index 2904.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 6, .distance 4 6, .distance 3 4, .distance 1 3, .theta 1]
    constant := ![3, -1, -1, -2, 2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 24 0, .gapLower 6 0, .gapLower 6 6, .triangle 32 0, .triangle 19 0, .corridorLower 1 3]

-- Original cycle 25d69ff540d01efee175fe22e9fd569c2aace348371d81a6f1e67684cf64ce7d; original global index 2905.
def localCycle00034 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 4, .distance 0 3]
    constant := ![2, 0, 0, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, true, false] }
  origin := ![.gapUpper 3 3, .triangle 11 2, .triangle 13 1, .gapLower 0 1]

-- Original cycle 26e9815e083d233f8f3b4ed40d0982e582b7da5b7d8ea11f57e14f3893ea4ce9; original global index 2981.
def localCycle00035 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .gapLower 4 0]

-- Original cycle 2704620bf03253aafba9fec85b824bac73a7501fa44627c57eda9db9dc3123ba; original global index 2992.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 274bfe138d77bf555efd6cac632d312dfea411545eeec0285cb06d7d7f24bd33; original global index 3009.
def localCycle00037 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 3 3, .triangle 32 1, .triangle 13 0, .gapLower 0 1]

-- Original cycle 2afd3d28cce8ebf12d4f082cf00f5fbe4deb859a96fd03398a356747af3b1d0f; original global index 3280.
def localCycle00038 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 2b9bc6cdb1246572da66b55ab7e6897259e31d8ed2884846c65d5566cba194d7; original global index 3334.
def localCycle00039 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 2, .distance 0 4, .distance 1 4, .theta 1]
    constant := ![3, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .triangle 8 1, .gapLower 0 2, .gapLower 4 2, .corridorLower 1 4]

-- Original cycle 2ca445bcbfe7f5fb7f1f4d1bcd4dc17e8f86ddc407ce22c9607a79615ef10cda; original global index 3413.
def localCycle00040 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 2d942570c5ab7b6d73c630b81823f53d7363c69367e200d6e27b161c5984543d; original global index 3472.
def localCycle00041 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 5 2, .triangle 14 2, .gapLower 0 4]

-- Original cycle 2fbd4b071b8528d26e4a460fc5f13a34860f089342718f22965da17292a8da1d; original global index 3649.
def localCycle00042 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 30406780557f7d32cb80e076280f7ef8fb6cbb40ac2c37e8f191ea50d3c686a4; original global index 3672.
def localCycle00043 : Cycle where
  length := 3
  data := {
    node := ![.theta 0, .distance 0 1, .theta 1, .theta 0]
    constant := ![1, -2, 0]
    coefficient := ![1, -1, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 6, .gapUpper 1 6, .thetaNext 0]

-- Original cycle 31eccd226f38bf60d79a54a95f294357ce39e916a890b09db80da566a5aeb256; original global index 3811.
def localCycle00044 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -3, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 3 2, .triangle 14 2, .gapLower 6 2, .triangle 18 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 32c0ed177b60dd9552575b0a46d8b1e8daa4c29d5ed93798d3740d6d992d271d; original global index 3886.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .theta 1]
    constant := ![3, -1, -2, 3, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 27 2, .gapUpper 2 6, .thetaNext 1]

-- Original cycle 3376642a96131b9eeacd645104478b0d06b24e6cd9a6624bcaf042eb97c0c52d; original global index 3937.
def localCycle00046 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 34b982be71f1b102a2638a432e7ae3c24f340308bc4f3ff372183fe092d8d118; original global index 4036.
def localCycle00047 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 35574ce519b0a1ea69615a3aca089042b47af89843c7e8f949d63dc879844826; original global index 4086.
def localCycle00048 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 4 2, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle 3614220a8b651ad5051a480e73cb065441c0ea84f321087a7adc72beeac2c004; original global index 4151.
def localCycle00049 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 2 4, .triangle 30 1, .triangle 14 0, .gapLower 0 3]

-- Original cycle 393f5dce4c35096d60baa06bd8dfa71374b39ca36f6518231c17a82160d4651c; original global index 4404.
def localCycle00050 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 4 6, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 34 1]

-- Original cycle 395632c6b68fa615d200deed4b3863ce82177e24f62a4253dc940f6854baaec8; original global index 4414.
def localCycle00051 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 0 5, .distance 0 2]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 2 5, .gapLower 5 3, .gapLower 0 4]

-- Original cycle 39c974694fd02dfd485631b16d926ffbbdcf70531202ff9928c415ad28f60ff2; original global index 4460.
def localCycle00052 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2]
    constant := ![4, -1, -1, -1, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3]

-- Original cycle 3a3a9c60e939b9a49959e1b9a5a969d2f51de25bdb986f151b565cb743c98120; original global index 4498.
def localCycle00053 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 3b9a922c34e93b43374b507fa83bce3bbbf684931c56ff0c713395d108168766; original global index 4605.
def localCycle00054 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 27 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 3bc6c1e4c2af0e921162fd96d64e93d66d91db0fe0ce643031d54afd762f5e3e; original global index 4624.
def localCycle00055 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 1, .gapUpper 5 1]

-- Original cycle 3cf1cd70e8093818e1128e72857098d19f674154b43ac64b97f7d46642cd2976; original global index 4719.
def localCycle00056 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 5, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapLower 6 2, .triangle 14 1, .triangle 7 1, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 3d93ac90057f6c0f8bfb0725d45b5410e6ac949eac5d595b019cc977928d7858; original global index 4767.
def localCycle00057 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 8 2, .gapLower 6 1, .gapLower 6 0]

-- Original cycle 3da3cab1071a8753d703155c1871305a5cb541ef2da61db692befcc0f4476fa1; original global index 4773.
def localCycle00058 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, -3, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 27 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 3dc55e1dcd3f1f2b9316350e702e64a65f7953465e3260943991d81e955c1af1; original global index 4782.
def localCycle00059 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 3f38e57884729131554e00d86704032084a832f9207d9edc7a6673530a8e2932; original global index 4882.
def localCycle00060 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 0 6, .distance 0 4]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 4 3, .triangle 13 2, .gapLower 0 2]

-- Original cycle 404300195f0b0286dd760c31ca40b94c3a3ca2aab823878c8e746c987224598e; original global index 4962.
def localCycle00061 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 13 2, .gapLower 6 2, .triangle 18 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 43d8b05f2b2a9080cd4316ee7da8ecb91ce49f978077ebcb6fe118e49bfaf734; original global index 5250.
def localCycle00062 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -1, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 44ad01dcfacfe6f75d7924dc6006e090bd0d7756265e07355168167681112bb4; original global index 5321.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 450f9cce64ba46069d986a2044e647694773eda761435ad3de5eb0214e50a026; original global index 5342.
def localCycle00064 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 23 1, .triangle 29 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 46dcf14868f9d8f896cf88f1da0166aa5917bdd40f660be3604ab35a75fb369a; original global index 5493.
def localCycle00065 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 4967b209ab89732a4122db95a6362eb2c4ee4158fb3c560177ee4001774f158e; original global index 5687.
def localCycle00066 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 4a7d00ef75c622a49ebdd34016681622011a7311212ecaad93dd73ca202b853b; original global index 5776.
def localCycle00067 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 4ac89ddeb1f17182d1e1e3181fbb040d40130cb064c177a511711471d490b809; original global index 5802.
def localCycle00068 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 13 2, .gapLower 6 1, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 4b6a84b174e8c50142275e2219edca759ffc6f44be97294d2fe0f686e8ffb6fc; original global index 5844.
def localCycle00069 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 4dd8c51d80b54966fff152494e77de4d5126da8332a0b2540392a97603ceb2cf; original global index 6043.
def localCycle00070 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 29 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 4fb6edf5c20d2771e5c0fe364d38c83cce9d0976bdae39be84d58a6110455a75; original global index 6190.
def localCycle00071 : Cycle where
  length := 3
  data := {
    node := ![.theta 5, .distance 5 6, .theta 6, .theta 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 0, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5000a344f7c79c397624161945c114ba558f9a2f9a9d79ad4db046cbe793078f; original global index 6213.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 0, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 50e9a5dea7e6b232e77aa311403ca2d0e22ba3bdbafbe4d2f7d4cd883d9f1dfc; original global index 6284.
def localCycle00073 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 2, .gapLower 0 2, .triangle 9 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 531dfcd80b106d6f21459935a614e21fdeabf0dc9e310232fdea4f7890606182; original global index 6467.
def localCycle00074 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 53a1ce2b8fcb58c497887d22c886831d9f98b842dd2c39d7d670d28f3cf9f709; original global index 6499.
def localCycle00075 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .gapLower 5 3, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 548514658dd0c16c318ebf50d0fafa00394c092825fe86c60dbb26a992ee9b2d; original global index 6550.
def localCycle00076 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .gapLower 5 2, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 5524315a6a7e0a94831e651da9fd9c06af4eaee31a9a534c61768759d9a4b1ef; original global index 6592.
def localCycle00077 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .gapLower 6 2, .gapLower 6 1, .triangle 18 1, .triangle 16 0, .gapLower 4 0]

-- Original cycle 55944a01859ee766a2c071fa5c065928c10d46b7d5e3851efa565e50f4a215a5; original global index 6632.
def localCycle00078 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 8 0, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 56004518c65f60aac00eff074008988c66f1b3c13e541fb2d8c4460d08035cea; original global index 6671.
def localCycle00079 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 598617078c41c46eecdc7d34ba1d292996b4af47ba522e67728ffcd7b1a751e6; original global index 6958.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 16 2, .gapLower 4 0]

-- Original cycle 59e0d6317bdb989a12683a1e7fde4aa0d830fed07c7d643559a4e9dfa3c9fa1a; original global index 6991.
def localCycle00081 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 5a1692244b523bb07038585f4a7af8dbe6a3ec5fef52eb820e506bdb65d7dfc3; original global index 7012.
def localCycle00082 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 5, .distance 0 2, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -2, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .triangle 14 1, .gapLower 0 3, .gapLower 2 3, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 5b54fb8247f86a6c15058a27068c85381c6433432cc546aad0dad959e1f6537e; original global index 7108.
def localCycle00083 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 5cb1734319521b97a02a904410c9d9e3bd50f21ea062d2edf154775a090bdfe1; original global index 7212.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 4 1, .triangle 18 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 5cd61694f127c91fed896dec404671b9d1eeba015dbeff17de906b69cd8da802; original global index 7225.
def localCycle00085 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5d3c02bec98845b639112eeff1b807c4dad1abf37b6524252fce84945f6241b6; original global index 7256.
def localCycle00086 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 5e460107ae90d43eba14ffc64ef116eb33a997b2eaa5dfaaf44fff7316b5924c; original global index 7334.
def localCycle00087 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 5e6c16176a690f0a0f8a9714996fb2c979a4b58336c53ccd696a248503dc8048; original global index 7347.
def localCycle00088 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 0 6, .distance 0 5, .distance 0 2]
    constant := ![2, 0, 0, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, true, false] }
  origin := ![.gapUpper 2 4, .triangle 8 2, .triangle 14 1, .gapLower 0 3]

-- Original cycle 60b7e676265ad7ed04362803a762fc03d09882076d06e432ceb26aa55bb56c07; original global index 7533.
def localCycle00089 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 4 3, .gapLower 0 1]

-- Original cycle 60bed6256c79f75d2c3404c8a72dc27ed045ee2b736ce1d429391d8b319f56db; original global index 7534.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 6164581f0d444335e855f0f7361034751a0366327037126d3a903fa0da1ced3a; original global index 7595.
def localCycle00091 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![4, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 18 0, .triangle 16 0, .gapLower 4 0]

-- Original cycle 61a065def47ef4e3687af1510bbf96e533f23aab69f558256f86d135d8174ecb; original global index 7617.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 3 0, .triangle 17 1, .triangle 18 0, .triangle 27 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 6254c4cb3e64b8e2f6a7579c4feee10cf97518338eb60780799f09ce4a8b615c; original global index 7676.
def localCycle00093 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 625be3cd075ed9e7a938674629335e8ef116827d72e36b3bd986118df1382399; original global index 7678.
def localCycle00094 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 0 6, .distance 0 4, .distance 1 4, .theta 1]
    constant := ![3, -2, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .triangle 7 1, .triangle 8 2, .gapLower 0 2, .gapLower 4 2, .corridorLower 1 4]

-- Original cycle 62bf6019fd0ddf860064147462171fcf6f809671c3b0487264449eece3c6209e; original global index 7707.
def localCycle00095 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 2]
    constant := ![-1, 0, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, true] }
  origin := ![.triangle 16 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .gapUpper 5 1, .triangle 17 1]

-- Original cycle 6606d5ee93f7f9e07ebb95f4d6c7e72d93443affab8988b8d50a4430b83d7354; original global index 7939.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 13 0, .gapLower 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 6837905f812d15c047e199d09522a49aebfb21f5ada3ab0bddf2f6c8deb769d4; original global index 8103.
def localCycle00097 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .triangle 8 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 692617ac15a1e9788fccee33eb2ab6b0ace157fc2fa9bdc4e22b82fd882c80e0; original global index 8177.
def localCycle00098 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 6954bac03a2f054554c2b09cc02b389fa96d645771463cb0438df8230fefb55b; original global index 8193.
def localCycle00099 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2]
    constant := ![4, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 23 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3]

-- Original cycle 69c4fd114cbbde71c6b006112ccb6cf3bf51063fb9c39e11dbc5722034fd9f22; original global index 8232.
def localCycle00100 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 5, .distance 1 5, .distance 1 2, .distance 2 6, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .gapLower 5 2, .triangle 17 1, .triangle 18 0, .triangle 27 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 6a3b4b1ad7583670a3d3dcdba3735ef38bf480f7fb54ae07af11543561157fe8; original global index 8270.
def localCycle00101 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 4, .distance 0 3]
    constant := ![2, 0, -2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 3 3, .triangle 11 2, .gapLower 0 2, .gapLower 0 1]

-- Original cycle 6b33230af8752f6ff78a6197feb9a569e2b3468a280d2e449d7997df9fad3b46; original global index 8344.
def localCycle00102 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 16 2, .triangle 19 1, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 6b6461a4c74e6eced678dc5859de01b7b5ed75ba036a13e6cb041da1316c4ca3; original global index 8359.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .gapLower 3 0]

-- Original cycle 6b69c9793e3b0a9b861869d7602793a9457ab02c7e81b9fa48f2c57fa092e715; original global index 8361.
def localCycle00104 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 6c1a7d9b914f18685b95147306809781411ac2128ecedf44471458f65f79bc41; original global index 8425.
def localCycle00105 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 6d49e415bc7d343db7bf2bacf2f8512c76ce052861f6bf2bb6fe3ca40fed0535; original global index 8497.
def localCycle00106 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 2, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 7013a3eb3a96dced0f0689601ebd1e6a2959ecc087fa7e9549ebfb7e91e780be; original global index 8689.
def localCycle00107 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 1 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 16 2, .gapLower 4 0]

-- Original cycle 714b8f89daf9b3358442a20c8011a69414ab8526f586427177c516b49357470f; original global index 8788.
def localCycle00108 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .gapLower 6 3, .gapLower 6 2, .triangle 18 1, .triangle 16 0, .gapLower 4 0]

-- Original cycle 7246b51e2c902698fbc74691592738e7012d94e360a6282bd366f08bbfaab159; original global index 8860.
def localCycle00109 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 4 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 13 2, .gapLower 6 1, .triangle 18 1, .triangle 16 0, .gapLower 4 0]

-- Original cycle 751f730bd2a187803a48ca78ea35d93755759ea74654c100ed852fcd5dbdaded; original global index 9075.
def localCycle00110 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 75281524e9c0a8abfdbe604a1ce0b33b4ca59e2b0e8efe105ecd4a666dd116f7; original global index 9078.
def localCycle00111 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 760474ca5f285e2e0b1fdc6bb3c34cd8b5eccdd8b70db183b9d6e682e87d8d4d; original global index 9141.
def localCycle00112 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 31 0, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .gapLower 3 0]

-- Original cycle 7874d5e4ced1937bc5a0825332acb075ec0ffa10d3668348fabf56109727266a; original global index 9316.
def localCycle00113 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 2, .triangle 18 1, .triangle 16 0, .gapLower 4 0]

-- Original cycle 7ae83c7379033f8fee4dcdc9610d09634d52c40fc6fe07eca3a4d671f68f7383; original global index 9514.
def localCycle00114 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 4 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 29 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 7ce1c4e585da787a4fedd41c91e1a213a5170801ca015dfc5bfe22514755e5ae; original global index 9672.
def localCycle00115 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 1, 0, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .triangle 8 0, .triangle 0 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 7e0d705d42a3d98047a8aeefd85ab9e6b7a55fa98279d3bfe719955654f76032; original global index 9789.
def localCycle00116 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .triangle 7 0, .triangle 0 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 7e288f5d32c0a54ce241fa1715457a1638716314ce592bcab7958d66e0718e90; original global index 9801.
def localCycle00117 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 4 2, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle 7e5d957ad83f3c6f02f128e1b2635929dd11d7d36129e51e1e41c4fc6fffc1b1; original global index 9815.
def localCycle00118 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 0 6, .distance 0 2]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 4, .gapLower 6 3, .triangle 8 1]

-- Original cycle 7f4d72cd49c242209482a38764ada5c157b9a45bfd010e5450d1b210ca75bbd1; original global index 9871.
def localCycle00119 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 801a00dd3960bbba3ff9ed671df611ba82c7c201177673988f2883117753a3ba; original global index 9936.
def localCycle00120 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 0 6, .distance 0 3, .distance 1 3, .theta 1]
    constant := ![3, -2, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .triangle 7 1, .triangle 8 2, .gapLower 0 1, .gapLower 3 2, .corridorLower 1 3]

-- Original cycle 81e7837041ec109e76c2ea61a3bf57c2346d857eb2f3640cfdb8aceca6b304ce; original global index 10086.
def localCycle00121 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 18 1, .triangle 16 0, .gapLower 4 0]

-- Original cycle 820becf8ab0cb415cc68072e35c2db2fc97e3ced29e3a0f8b6895c820af0e289; original global index 10096.
def localCycle00122 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 27 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 85557c35e65a16a3bc11d0aeb9ab0dab3c064f0035e74a453fab4e3bac04a98b; original global index 10343.
def localCycle00123 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 3, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .gapLower 3 0]

-- Original cycle 856c120998be23e43ce0654cf12d202700fad123420e5d419b1bad2929462634; original global index 10350.
def localCycle00124 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 1 3, .theta 1]
    constant := ![3, -1, -3, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 19 0, .corridorLower 1 3]

-- Original cycle 85875a8c5919fe32aeef88d3cc5e217549c2d61edd05b348dc5a11f922902c38; original global index 10361.
def localCycle00125 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 0 6, .distance 0 5, .distance 0 2]
    constant := ![2, 0, -2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 2 4, .triangle 8 2, .gapLower 0 4, .gapLower 0 3]

-- Original cycle 869510e916bb0d1b997fc820a6e3c1fb3505bbb8558f42de418527a585a917c7; original global index 10435.
def localCycle00126 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 14 0, .gapLower 0 3, .triangle 6 2, .triangle 9 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 87ef0d373bf60409f15f10e9b7f3d7f8b1de0312a309c71edb3671b30cd2a11d; original global index 10534.
def localCycle00127 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -3, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 89dd0eb4e5a74e4fbd1dd2dcd390b60b3648cbdd4cb3c9b55b53b992c329a50f; original global index 10680.
def localCycle00128 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 8a5f5f91fd30c8de88a590c1eec83242d9b5f149ca549488cd50dab47fc19777; original global index 10722.
def localCycle00129 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .gapLower 6 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 8c9c8a9b9b915c22c3e5b9443ab71a1dd8c381d46bcf4fa0e61627f7ba8fd4ed; original global index 10878.
def localCycle00130 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 8d0897ff8e059b2dd1741a3fbd336e84bbb72d8eeb4e7fa48c97bd741ff33204; original global index 10908.
def localCycle00131 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 2 6, .distance 0 6, .distance 0 4]
    constant := ![2, -3, 0, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.gapUpper 4 3, .gapLower 6 4, .triangle 8 2, .triangle 13 1]

-- Original cycle 8d7c6114cf681c0bd3a95967577c4cec4e25e9d5e4572bb3be29a33a3e77da3a; original global index 10940.
def localCycle00132 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 1 2, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 0 1, .triangle 16 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 8debfabe7c7b8d3d96245a84b40fccd7761d95f7eb2279939268665b675ec5ae; original global index 10988.
def localCycle00133 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 2, 0, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 8eb3b01c0feafc3c22b93cad1e60f2d084f57c8db5d6a6543feb0de2752d4e7c; original global index 11042.
def localCycle00134 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 31 0, .triangle 34 0, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 16 0, .triangle 15 0, .gapLower 3 0]

-- Original cycle 8f3ba9b77e1e65040d4f24163c363c21cf045a0b611711dffef0b924b8c927a0; original global index 11083.
def localCycle00135 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 5, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .theta 0]
    constant := ![2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 12 1, .triangle 13 0, .triangle 23 0, .gapLower 1 1, .corridorLower 1 3, .thetaNext 0]

-- Original cycle 8f8c26cbeb052b49c7ca4af04d4d248273e2efe9fd5d730611810d39dc9e6e9f; original global index 11109.
def localCycle00136 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 5, .distance 1 5, .theta 1]
    constant := ![3, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .gapLower 0 4, .gapLower 5 1, .corridorLower 1 5]

-- Original cycle 8ffb17d66bb5439fe7d40a80335edbb28ddebdaae19415a4b64214c1ba71d45b; original global index 11146.
def localCycle00137 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 8 0, .triangle 18 0, .triangle 16 0, .gapLower 4 0]

-- Original cycle 90e722e8ff746b453d69e631f88d2146a2fcc6a0e16d6545f83d6fdbb52fbd09; original global index 11220.
def localCycle00138 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 9180bd9ae7cc1eec1073259c4b698bc6218209ffa2bf03d15e12e6aab0da4f6b; original global index 11270.
def localCycle00139 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 18 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle 9257848b174cf892965b384908a85d389fd71e3bd1f63ee2d1a9bc16be3665d4; original global index 11336.
def localCycle00140 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 24 0, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 93a03e42e11b773dd391b53475013d05580b43ae6a0d67c596fcb0762b93cd77; original global index 11452.
def localCycle00141 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 29 1, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 954e916109ae6017f3eb54eb904c7f43d4f37ddcebf628d369d44b4c68734cdb; original global index 11598.
def localCycle00142 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 1 2, .distance 2 6, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -2, -2, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .gapLower 0 4, .gapLower 2 4, .triangle 18 0, .triangle 29 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 95520f92c5165c7ef7adb4a35060f6745149137b98a4c37956314f527bb3137f; original global index 11601.
def localCycle00143 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 9b06ec6e7f39d16b5c1f9eccfbe4b15f7f41b2b7f0ad42db4dc6437a760426c5; original global index 12050.
def localCycle00144 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 9c3489fd8db55eeaafc228628913fc842887c767c907bc7ce27ac8bafaa6e8f9; original global index 12152.
def localCycle00145 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 9cbb58ead9b1d26e23f8750ed28c5be734c3be32e141042402b6c30aa5b5dbb3; original global index 12190.
def localCycle00146 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 7 0, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 9ccd4f356adf7014bf347822d01b788f9919ab228cdd33273fcee52984727689; original global index 12196.
def localCycle00147 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .corridorLower 4 6]

-- Original cycle 9d676743d4f6bbb339fa13fb4a1dd93490540ca8f77118a4e49d2a721b1f48ad; original global index 12242.
def localCycle00148 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .gapLower 6 3, .triangle 4 1, .triangle 18 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 9dec3ed9aa624df4a7faffe79cb3f5782c2c1977eb2ca442e18ba4bd591fe97c; original global index 12289.
def localCycle00149 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 13 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 9e4b667865e12d7b94e4085aabb4b47d7b8a560512ee75a6dd124f7a6949ba9b; original global index 12323.
def localCycle00150 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, -2, 0, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .triangle 7 1, .gapLower 0 3, .gapLower 4 3, .triangle 23 0, .gapLower 1 1, .corridorLower 1 3]

-- Original cycle 9e807085274909a9a0eb05d01e7bff63d83b33a8cb868ae4e84e92173a6c7ec2; original global index 12345.
def localCycle00151 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 2, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 9e8269f1c95a9c521a339ad678f779d6d7ff8af51076ecf39dff5f9003b36326; original global index 12346.
def localCycle00152 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .theta 1]
    constant := ![3, -1, -2, 3, 0, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapUpper 2 6, .thetaNext 1]

-- Original cycle a10a7108c95d1b63efae227ef44347dbaa08ac447c695def6f380aeedf7b0233; original global index 12524.
def localCycle00153 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 4 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 29 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle a219396016780754e613446cbe7a43ce79cc4d476613d758941413ccd4f30751; original global index 12610.
def localCycle00154 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .theta 2, .theta 1]
    constant := ![3, -1, -2, 3, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, -1, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 2, .gapUpper 2 6, .thetaNext 1]

-- Original cycle a2580028ed0fefc8bd45bd9d3be2c50f2eb17bf2b73497606bff1d3fe351fb79; original global index 12632.
def localCycle00155 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle a405b29944ee2ac16f50a9c53a698f3fe8cfacba8cbde90b8d06b8793363ab8d; original global index 12753.
def localCycle00156 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -3, 3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle a4b99c930fe8a7dd143664f5db0bfc161cf0ba02cf3d135315dd82db59038b0b; original global index 12802.
def localCycle00157 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle a4c7da6a689dd91e3dfc2746369dca5accdc04f0ccb2bbdf0ba8cda6c1e406cc; original global index 12807.
def localCycle00158 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 2, .triangle 7 0, .triangle 0 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle a4f247aee7b47606e911bc325eb61d1e450e2af8de74bdd8da32130b710ca02c; original global index 12817.
def localCycle00159 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle a569b568d233d55cc77905dc054be430a885f26920b7acf3660a3f8890256864; original global index 12851.
def localCycle00160 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle a6f98f71efb24971d37dda8c69bfbad9885ce525de60b37cc1baa5a201040eaa; original global index 12977.
def localCycle00161 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 13 0, .triangle 9 1]

-- Original cycle a7bf28614c07737197553da8c1930c6d13bea295ea01bc2ddef0b2e8bb910915; original global index 13050.
def localCycle00162 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 14 2, .gapLower 0 4, .triangle 12 1, .triangle 9 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle a7f95da4608cccb2b212304880ccb43f8b2fdedf821058ee2402a09c13eaffc1; original global index 13076.
def localCycle00163 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 2, .triangle 13 1, .gapUpper 4 3]

-- Original cycle a8f4c74c954ed4ff6a35ef4f7d253fec31d946e865dff617df3eea0269965db2; original global index 13153.
def localCycle00164 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 27 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle a92fa543a2cab5245df79b3b728874a006164725b827edc997cb5ba0af1e15f8; original global index 13171.
def localCycle00165 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 4 3, .gapLower 0 1]

-- Original cycle a9707215f99a8e69d5fcd6ef958d61def534f35a301e1e20c240afc21aadd29c; original global index 13190.
def localCycle00166 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 3 6, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 33 1]

-- Original cycle aaee592b9ca8d2115d9bfd2868aebe31cceb3107c9a7bd05d3b8bf72fb2abace; original global index 13314.
def localCycle00167 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 17 1, .triangle 16 2, .triangle 23 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle ab30e26e1f51eb27efd2bd77e7ec4e904d2ea947021f1586f6917cc6488b31ac; original global index 13335.
def localCycle00168 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 1 5, .distance 0 1]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 3 1, .gapUpper 1 5]

-- Original cycle ab3601535e7b5166cda11d69629b50f49d945b39b73970a2a84708ab7255d7c4; original global index 13339.
def localCycle00169 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 5, .distance 0 2, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 2, .triangle 7 0, .triangle 0 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle abcc50abe9d966fb9cfd4b26e845fdfc99092d2a94d3a41e29afc6dcb6e50173; original global index 13375.
def localCycle00170 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 30 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle ade312af58474fbdae8d24b7061f586fab4edd7a89a11d6ebba9a2500d1f60fc; original global index 13567.
def localCycle00171 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![4, -2, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.gapLower 2 6, .gapLower 6 2, .gapLower 6 1, .triangle 18 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle ae0d3e85487a3700c2f89194323281ab4f27357163cd310e32a75bdaf2626b95; original global index 13581.
def localCycle00172 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle ae90eba61d4dac8c176504a78f4840f7e8fbd3f2be6039bf2d2c4d1d72e872c9; original global index 13626.
def localCycle00173 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle aea0ba84e05bb5afd639efdf13b7b70f88df7c51f977c3011e85e41938ff4231; original global index 13630.
def localCycle00174 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 2, .triangle 8 0, .triangle 0 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle af05958806f1ae9b98334cdf2d3778c3a3869f961766cb8151a72d43d4e05a36; original global index 13661.
def localCycle00175 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 2 5, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![4, -1, -3, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 7 0, .gapLower 0 3, .triangle 13 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle af0d6e9717ad64d30d3c037f28f7017d827030706c2e7ec10522896a9d2196ca; original global index 13666.
def localCycle00176 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .gapLower 6 2, .triangle 4 1, .gapLower 6 0]

-- Original cycle afb6cd6298841bdfefc8bd7fe19a6e0289fac4b8c92b6c5f9ee7f87e4867257d; original global index 13725.
def localCycle00177 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 1 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .gapLower 0 3, .triangle 4 1, .triangle 18 1, .triangle 30 1, .corridorLower 5 6]

-- Original cycle b0a382bc11f879612d41c8ac887af738148c0ccaccd436d39c4a4424887bca2a; original global index 13792.
def localCycle00178 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -2, 0, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .triangle 4 1, .triangle 24 1, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle b1595f0e00cb49bfd608f30ea21fc0e20bb36752e3780b84e3c161b706b8a7e0; original global index 13854.
def localCycle00179 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 0 3]
    constant := ![2, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 29 2, .gapLower 6 3, .triangle 11 1]

-- Original cycle b33bd8a847d3c2c1f973ef9adade91d4b981b58aa65c88f8efe2c94a3aa06e76; original global index 14008.
def localCycle00180 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, 0, -2, 0, 0, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, true, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 27 2, .gapLower 6 2, .triangle 4 1, .triangle 24 1, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle b3ed3411e2678a936ea66551a0a9e3aaf153a6111033e4ce28015db864f12846; original global index 14050.
def localCycle00181 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 2, .triangle 8 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle b73376aa331c64a55bcbe65e00994a4acd676ac0328c089a1a8b603a2f105ac6; original global index 14303.
def localCycle00182 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b974563bfb4b6758e19a2283bae481c55616fcc3481cb13420205e533c377068; original global index 14470.
def localCycle00183 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 0 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle b9df6c105616e0a3dd31ab0e6d60dbc4081d7d02a7dbf7e03a595080cbebce3d; original global index 14511.
def localCycle00184 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle bb3d75e8f886e848f8683b5ed815be153ef2e6405077ce7fd1ef57dd5c958b49; original global index 14621.
def localCycle00185 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 2, .triangle 13 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle bba43d0b39b19f1c86ebb42df48b35b8c188c7a91a2a8d25e18326985388ffc8; original global index 14649.
def localCycle00186 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, -2, -2, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .gapLower 6 2, .triangle 4 1, .triangle 18 1, .gapLower 2 2, .gapLower 4 0]

-- Original cycle bc079b4cee057452319d2b714785665a8d79f67522bc971a8bf499e69fc2627c; original global index 14682.
def localCycle00187 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 5, .distance 0 2, .distance 0 4, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .theta 0]
    constant := ![2, 0, 0, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, true] }
  origin := ![.gapLower 0 6, .triangle 3 2, .triangle 7 1, .triangle 6 2, .gapLower 0 2, .triangle 13 1, .triangle 23 0, .gapLower 1 1, .corridorLower 1 3, .thetaNext 0]

-- Original cycle bd9b40e6eb92b4fd7525a2c671417cb4a83f546ff633dab3797266b173c52a76; original global index 14789.
def localCycle00188 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .gapLower 4 0]

-- Original cycle bf2518ba8a10c066ac984c05927a956a2a3f644aceadb1dee42d779c5b0d1908; original global index 14915.
def localCycle00189 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, -2, -2, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .gapLower 0 4, .triangle 6 2, .triangle 13 0, .triangle 23 0, .gapLower 1 1, .corridorLower 1 3]

-- Original cycle c03735bcbc18bf4f35c456613462f70807acd41edb9af6a9c36947300f810c1c; original global index 15008.
def localCycle00190 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 3, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c0a7945a224325096b9f6613c913318e024433f79e03a4fe5e938222a7b8fa94; original global index 15044.
def localCycle00191 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle c196da342e06ddb7cf769424a8d264d138c962e997f05f1917bab9d8bafa601f; original global index 15120.
def localCycle00192 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c226c7f85ab37c3d5ab45a0a8a77ea47537e6f74b5725333e1466ee24870d2af; original global index 15159.
def localCycle00193 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c2cfba8a50baf14dd9f313a5ccc76ebd7971cae7965a230df962a777031ee73e; original global index 15203.
def localCycle00194 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 3]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 3 3, .triangle 11 2, .gapLower 0 1]

-- Original cycle c483818bf6d08b4d0afbb55d24b841f24eceea18f43ed57d770ac2b0fa9a1676; original global index 15325.
def localCycle00195 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle c54e35e33c3db4bcb30257ec08275ff74206f0dcc794e6537e1d4a8a07d81b78; original global index 15393.
def localCycle00196 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 16 0, .gapLower 4 0]

-- Original cycle c810bd76b74d4ed6601c3fdbe0d265809863f98edcb06ed01135ced4a03fede3; original global index 15620.
def localCycle00197 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 3, .thetaLower 0]

-- Original cycle ca80298887cf963d097aa501f2785147a57c22adfd3d46543b52b8f8705f672c; original global index 15826.
def localCycle00198 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 5, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 27 2, .gapLower 6 2, .triangle 14 1, .triangle 7 1, .corridorLower 0 2, .thetaLower 0]

-- Original cycle ca8a061bbed47eb5c653e74878c9b7064402c1f33f335bb5d3e4fc127689a276; original global index 15829.
def localCycle00199 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 1, .gapUpper 5 1]

-- Original cycle cd05bdc16dd563b0a8f0aa3685cca8bdb2e816b2ca5d79300b5b539aac502a9b; original global index 16022.
def localCycle00200 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 32 2, .gapLower 6 3, .gapUpper 2 6, .thetaLower 2]

-- Original cycle cf549eeabba4580072cd89168de67b3224c54e20244d0674f0d5b1a602098bb9; original global index 16182.
def localCycle00201 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 16 2, .triangle 23 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d19693f9829e00c1c39620a248c6acde6c494cb8e955feb57cc334f68d25bfac; original global index 16357.
def localCycle00202 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -1, -3, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .gapUpper 2 6, .thetaLower 2]

-- Original cycle d2a433c32d67910ea36800334754f536a7e9777be2d9c6ad7ba219f8777474f2; original global index 16438.
def localCycle00203 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 0 3, .distance 1 3, .theta 1, .distance 0 1, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -1, -1, -1, 0, -1, 3, 0, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 0, .triangle 31 0, .triangle 9 0, .triangle 1 1, .corridorLower 1 3, .corridorUpper 0 1, .triangle 4 2, .gapLower 6 1, .triangle 24 1, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle d32cae771064c5cd1d0fb8621fd98956496f4013c39a812353f2d93263e4d99d; original global index 16473.
def localCycle00204 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle d36d8f963e7dcb739e611ab952a78d859843fcc640f9fa168c94e20d46822150; original global index 16492.
def localCycle00205 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 8 0, .triangle 0 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle d47246980d083d97656f2c5516d6092505c49158bb94b024f93bcb43707ee6d8; original global index 16576.
def localCycle00206 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .gapLower 6 3, .triangle 4 1, .triangle 18 1, .triangle 16 0, .gapLower 4 0]

-- Original cycle d566c6bd8c2fbe57fbc4a0c074ec29832d1e7b82f66a06e4f19473c2d9e8a3d6; original global index 16655.
def localCycle00207 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 4, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -2, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .gapLower 0 3, .gapLower 0 2, .triangle 13 1, .triangle 23 0, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1]

-- Original cycle d56fbf8c247e06cc4df213299e338d839a957756ee379ae061021a6e4cd3311c; original global index 16662.
def localCycle00208 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, 0, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .triangle 8 2, .gapLower 6 2, .triangle 18 1, .triangle 16 0, .gapLower 4 0]

-- Original cycle d81df5cbc1cf9241d36bad843ddbc094d0476ec3759fc9e9ddc7a44112c4ffcc; original global index 16869.
def localCycle00209 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 4 1, .gapUpper 1 5]

-- Original cycle d902e72188f29333d305196874eb1e747ba389c326451f57662aa597bf16c6fa; original global index 16949.
def localCycle00210 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .gapLower 5 3, .triangle 7 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle d91a550c57d410504560693db9b087cb7f0a331329265070a43f6449a6aefcbb; original global index 16963.
def localCycle00211 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .gapLower 6 2, .triangle 4 1, .triangle 18 1, .triangle 16 0, .gapLower 4 0]

-- Original cycle da0aec30d28c51b425e971a5d53f606f61b4069bdec7b26e13f00227a50e3d34; original global index 17038.
def localCycle00212 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 16 2, .triangle 23 0, .triangle 34 1, .corridorLower 5 6]

-- Original cycle dacfd030a272c8f9426a8526080c5f723fc9cd31fb87b03a106e1e939b85f71b; original global index 17100.
def localCycle00213 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 29 0, .corridorLower 4 6]

-- Original cycle dc4f2836145ee8fbe5851f3d337533f7323c2ccfedfff073fbedcabcd2300fef; original global index 17216.
def localCycle00214 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 5, .distance 0 2, .distance 0 4, .distance 1 4, .theta 1]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 4 2, .gapLower 0 4, .triangle 7 1, .gapLower 0 2, .gapLower 4 2, .corridorLower 1 4]

-- Original cycle dcd6be629f851c60f3dda9ddb8c55581d334282bb6f75a6bae998e1d67541926; original global index 17258.
def localCycle00215 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle dce2becb9e5415d0398c67b7869a0bf279800fcdaf0238f235e56aeed67c7e59; original global index 17264.
def localCycle00216 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 29 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle dd9f75c8e30e95fc972ed51c84558b1f6e3a6b4887bcfa795fd7b0dd443c8df9; original global index 17323.
def localCycle00217 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 8 2, .gapLower 6 1, .triangle 24 1, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle ddc1cf22b9e5328eb78323ec5df0d2ac603c9bb8be67122aa57b62dc4fe44390; original global index 17333.
def localCycle00218 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 0 3]
    constant := ![2, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .triangle 8 2, .triangle 11 1]

-- Original cycle e4a6ab4a92a462219e4a849b8303ec2aa24e3c80f7a9610af5086d948a54fed5; original global index 17873.
def localCycle00219 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 0 6, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 13 2, .gapLower 0 2, .triangle 9 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle e4abe7966e5335653492190850299b76e0048e1e9d34a7e077041118ad16aaa7; original global index 17878.
def localCycle00220 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 4 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, -3, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 29 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle e4d5b2ad5066aa7f6b2a0199839ff68c4d5ec13fa1908e8b34c753103522b0fa; original global index 17888.
def localCycle00221 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .gapLower 6 1, .corridorLower 1 6, .thetaLower 1]

-- Original cycle e588a7d3099c78f5c81d4df5f0fa69dd736de92fa56960a39bc8015419eaf8f9; original global index 17954.
def localCycle00222 : Cycle where
  length := 13
  data := {
    node := ![.theta 0, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .theta 0]
    constant := ![2, -1, 0, -1, 0, -1, 3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 6, .triangle 3 0, .triangle 17 1, .triangle 18 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 23 0, .gapLower 1 1, .corridorLower 1 3, .thetaNext 0]

-- Original cycle e6d3753f8ca03c66924d3701aca14227c5b7199dd5715341eb97afda34083180; original global index 18060.
def localCycle00223 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle e7332a80efb5131d3fa3edc26dd109d6849596dac2785f387d1f780839636785; original global index 18084.
def localCycle00224 : Cycle where
  length := 13
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle ea53ff9f711b4e48642685e862d4ec67fb85602438e0c1e211979acf69685402; original global index 18301.
def localCycle00225 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .gapLower 0 2, .triangle 11 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle ea9732dbbd2cee3a51f9326bb7fb73f6389038d0b2cf9df0951418ab327b559f; original global index 18324.
def localCycle00226 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 3]
    constant := ![4, 0, -1, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 7 0, .gapLower 0 3, .triangle 13 0, .triangle 29 0, .gapLower 2 1, .gapLower 3 0]

-- Original cycle ead79f953eb9d3f8c6729a23c5f3999f41725a7fd82e32549248c207c931d1f7; original global index 18344.
def localCycle00227 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 1 5, .distance 0 1]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 5, .gapLower 5 2, .gapUpper 1 5]

-- Original cycle eb9e7f50095b9a25d557bde4098450798d40e4342021543dc548e8a1e7cc3545; original global index 18384.
def localCycle00228 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .gapLower 5 3, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle ec73fad42ad241489157b0d7cd8065cf4ec7058a5fa055e3d2903f20d2060690; original global index 18454.
def localCycle00229 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 4 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, -2, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .gapUpper 2 6, .thetaLower 2]

-- Original cycle ed77e966dfb64c8194aa2b5d10bb19fb2d47d94ee73c836dab79345d2fc7d5d7; original global index 18536.
def localCycle00230 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle f100bb92a28f46dcce849b8ddb33f8cb22b18ea7e4f3d631eae5c1b0c30aea7a; original global index 18797.
def localCycle00231 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle f1d717ea282173538a507ddb73dc1c7f94404d2df31a3b9e36de6f6547781e63; original global index 18857.
def localCycle00232 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 13 0, .triangle 9 1]

-- Original cycle f1ef8e1bdb7c855d0797c384cbfd2ab8bbd185eba175765265a873bac8e6f925; original global index 18867.
def localCycle00233 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 11 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle f3840f5bc3dba0a74100741c2eade1420cfea74d04bf0c83ea61f95aedd0936e; original global index 18998.
def localCycle00234 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .triangle 8 2, .gapLower 6 1, .triangle 18 1, .gapLower 2 2, .gapLower 4 0]

-- Original cycle f3c6220ee036775892337abe467cd79d149724c01f62562a2d7ccb7dd0009f90; original global index 19016.
def localCycle00235 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle f5dde0ce299c06e7d37f6bba3c3452c5ef9b18479838406cfd31f293d7b97bc9; original global index 19184.
def localCycle00236 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, -2, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .triangle 12 1, .triangle 13 0, .triangle 23 0, .gapLower 1 1, .corridorLower 1 3]

-- Original cycle f65fd33632d646e76c50f1a0a7ef12f31cd88b83d4a178dbd18b325a4aa5b826; original global index 19217.
def localCycle00237 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 6, .distance 0 5, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -2, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 4 2, .gapLower 0 4, .gapLower 5 1, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle f693830174561d8b192f5e09f0c3bb7bd399541ab308f29768613d9881bcc740; original global index 19239.
def localCycle00238 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle f9b72ca6e6272dd3b88e11b51ed7d2ee2e0bc29d42feb1614f9100d15fbf3173; original global index 19468.
def localCycle00239 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -2, 2, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .gapLower 6 6, .triangle 30 0, .triangle 7 0, .triangle 0 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle fb5613d6b4944daf75dbe8649f5cae2a83ddd17aabdbfde29a1dfbe68355c610; original global index 19615.
def localCycle00240 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle fb9c642f23929668099bd4fe75e8c3f5ca9cd891692251fec92a84c3668f75ac; original global index 19644.
def localCycle00241 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 3, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle fd5917fbb4a0af84ea5b85c72196f7c1ec4cecc40e39a0a37f7398f7b1bf33bd; original global index 19800.
def localCycle00242 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 2]
    constant := ![-1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 16 0, .triangle 29 0, .triangle 34 1, .gapUpper 5 1, .triangle 17 1]

-- Original cycle fed5fd336505b8ae407a403341070d9acbd54db51a67b18c884eea94fc7f7096; original global index 19925.
def localCycle00243 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 0 5, .distance 0 2]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 2 5, .gapLower 5 3, .gapLower 0 4]

-- Original cycle ff6e03fdc9105aa89eef350eef274b706fd4622f19830a0c4e3b1adaac14906d; original global index 19971.
def localCycle00244 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 5, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 2, .triangle 14 2, .gapLower 6 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle ffef4270d44c867414521c792325f8848380b1cfbccf8d738f2bd1294737810d; original global index 20019.
def localCycle00245 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

def library : Library := fun id => if id < 123 then (if id < 61 then (if id < 30 then (if id < 15 then (if id < 7 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 5 then (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)) else (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)))) else (if id < 11 then (if id < 9 then (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none)) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none))) else (if id < 13 then (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none)) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))))) else (if id < 22 then (if id < 18 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none))) else (if id < 20 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)))) else (if id < 26 then (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none))) else (if id < 28 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none)) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)))))) else (if id < 45 then (if id < 37 then (if id < 33 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))) else (if id < 35 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none)))) else (if id < 41 then (if id < 39 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))) else (if id < 43 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))))) else (if id < 53 then (if id < 49 then (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none))) else (if id < 51 then (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none)) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)))) else (if id < 57 then (if id < 55 then (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none))) else (if id < 59 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none)) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))))))) else (if id < 92 then (if id < 76 then (if id < 68 then (if id < 64 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))) else (if id < 66 then (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)))) else (if id < 72 then (if id < 70 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none))) else (if id < 74 then (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none))))) else (if id < 84 then (if id < 80 then (if id < 78 then (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none))) else (if id < 82 then (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none)) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)))) else (if id < 88 then (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none))) else (if id < 90 then (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)))))) else (if id < 107 then (if id < 99 then (if id < 95 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none))) else (if id < 97 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)))) else (if id < 103 then (if id < 101 then (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none))) else (if id < 105 then (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none))))) else (if id < 115 then (if id < 111 then (if id < 109 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none))) else (if id < 113 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none)) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none)))) else (if id < 119 then (if id < 117 then (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none))) else (if id < 121 then (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none)) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none)))))))) else (if id < 184 then (if id < 153 then (if id < 138 then (if id < 130 then (if id < 126 then (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none))) else (if id < 128 then (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none)))) else (if id < 134 then (if id < 132 then (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none)) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none))) else (if id < 136 then (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none)) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none))))) else (if id < 145 then (if id < 141 then (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none))) else (if id < 143 then (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none)) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none)))) else (if id < 149 then (if id < 147 then (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none)) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none))) else (if id < 151 then (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none)))))) else (if id < 168 then (if id < 160 then (if id < 156 then (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none))) else (if id < 158 then (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none)) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none)))) else (if id < 164 then (if id < 162 then (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none)) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none))) else (if id < 166 then (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none)) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none))))) else (if id < 176 then (if id < 172 then (if id < 170 then (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none)) else (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id = 171 then some localCycle00171 else none))) else (if id < 174 then (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id = 173 then some localCycle00173 else none)) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id = 175 then some localCycle00175 else none)))) else (if id < 180 then (if id < 178 then (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none)) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none))) else (if id < 182 then (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none)) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id = 183 then some localCycle00183 else none))))))) else (if id < 215 then (if id < 199 then (if id < 191 then (if id < 187 then (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none))) else (if id < 189 then (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none)) else (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none)))) else (if id < 195 then (if id < 193 then (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none)) else (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none))) else (if id < 197 then (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none)) else (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id = 198 then some localCycle00198 else none))))) else (if id < 207 then (if id < 203 then (if id < 201 then (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id = 200 then some localCycle00200 else none)) else (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none))) else (if id < 205 then (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id = 204 then some localCycle00204 else none)) else (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id = 206 then some localCycle00206 else none)))) else (if id < 211 then (if id < 209 then (if id < 208 then (if id = 207 then some localCycle00207 else none) else (if id = 208 then some localCycle00208 else none)) else (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id = 210 then some localCycle00210 else none))) else (if id < 213 then (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id = 212 then some localCycle00212 else none)) else (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id = 214 then some localCycle00214 else none)))))) else (if id < 230 then (if id < 222 then (if id < 218 then (if id < 216 then (if id = 215 then some localCycle00215 else none) else (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id = 217 then some localCycle00217 else none))) else (if id < 220 then (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id = 219 then some localCycle00219 else none)) else (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id = 221 then some localCycle00221 else none)))) else (if id < 226 then (if id < 224 then (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id = 223 then some localCycle00223 else none)) else (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id = 225 then some localCycle00225 else none))) else (if id < 228 then (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id = 227 then some localCycle00227 else none)) else (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id = 229 then some localCycle00229 else none))))) else (if id < 238 then (if id < 234 then (if id < 232 then (if id < 231 then (if id = 230 then some localCycle00230 else none) else (if id = 231 then some localCycle00231 else none)) else (if id < 233 then (if id = 232 then some localCycle00232 else none) else (if id = 233 then some localCycle00233 else none))) else (if id < 236 then (if id < 235 then (if id = 234 then some localCycle00234 else none) else (if id = 235 then some localCycle00235 else none)) else (if id < 237 then (if id = 236 then some localCycle00236 else none) else (if id = 237 then some localCycle00237 else none)))) else (if id < 242 then (if id < 240 then (if id < 239 then (if id = 238 then some localCycle00238 else none) else (if id = 239 then some localCycle00239 else none)) else (if id < 241 then (if id = 240 then some localCycle00240 else none) else (if id = 241 then some localCycle00241 else none))) else (if id < 244 then (if id < 243 then (if id = 242 then some localCycle00242 else none) else (if id = 243 then some localCycle00243 else none)) else (if id < 245 then (if id = 244 then some localCycle00244 else none) else (if id = 245 then some localCycle00245 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .tail 238 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20992)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 5, 6], ![2, 1, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 4, 3]], proof := .tail 130 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20993)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 4, 3]], proof := .tail 38 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20994)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 4, 3]], proof := .tail 181 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20995)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 4, 3]], proof := .tail 181 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20996)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 0, 3, 4]], proof := .tail 141 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20997)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 0, 4, 3]], proof := .tail 31 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20998)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 0, 6, 4, 5], ![1, 2, 6, 0, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 4, 0, 3]], proof := .tail 66 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20999)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 0, 6, 4, 5], ![1, 6, 2, 0, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 2, 0, 3]], proof := .tail 52 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21000)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 6, 0, 4, 5], ![1, 2, 6, 0, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 4, 3, 0]], proof := .tail 105 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21001)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 6, 0, 4, 5], ![1, 6, 2, 0, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 2, 3, 0]], proof := .tail 52 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21002)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .tail 141 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21003)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 0, 4, 3]], proof := .tail 31 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21004)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 0, 6, 4, 5], ![1, 2, 6, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 4, 0, 3]], proof := .tail 66 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21005)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 0, 6, 4, 5], ![1, 6, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 2, 0, 3]], proof := .tail 99 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21006)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 0, 6, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 2, 0, 3]], proof := .tail 212 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21007)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 4, 0, 5], ![2, 1, 0, 6, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 2, 1, 0, 3]], proof := .tail 231 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21008)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 6, 0, 4, 5], ![1, 2, 6, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 4, 3, 0]], proof := .tail 105 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21009)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 6, 0, 4, 5], ![1, 6, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 2, 3, 0]], proof := .tail 99 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21010)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 6, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 2, 3, 0]], proof := .tail 65 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21011)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 4, 0, 5], ![2, 1, 6, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 2, 1, 3, 0]], proof := .tail 231 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21012)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![6, 3, 2, 4, 5, 0], ![3, 6, 1, 4, 0, 5], ![2, 6, 1, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 231 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21013)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![6, 3, 2, 4, 5, 0], ![6, 3, 1, 4, 0, 5], ![6, 2, 1, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 5 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21014)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 5, 6], ![2, 1, 0, 4, 5, 6], ![2, 1, 0, 3, 5, 6], ![1, 0, 2, 3, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .low6 (![124, 117, 29, 127, 58, 50, 157, 57, 176, 152, 45, 20, 30, 171, 217, 11, 68, 203, 56, 198, 216, 8, 13, 200, 133, 122, 54, 70]) }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21015)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 5, 6], ![2, 1, 0, 4, 5, 6], ![2, 1, 0, 3, 6, 5], ![1, 0, 2, 3, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 169 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21016)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 5, 6], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 3, 4]], proof := .tail 183 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21017)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 3, 4]], proof := .low0 (![215, 165, 195, 88, 41, 209, 43, 89, 18, 126, 162, 178, 10, 32, 89, 89, 89, 89, 76, 214, 39, 4, 125, 82, 49, 136, 237, 84]) }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21018)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 3, 4]], proof := .tail 72 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21019)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low6 (![71, 199, 44, 118, 74, 6, 173, 7, 244, 19, 85, 46, 33, 97, 36, 235, 23, 55, 172, 59, 204, 61, 90, 230, 148, 91, 205, 16]) }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21020)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 5, 6], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 4, 3]], proof := .tail 116 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21021)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 4, 3]], proof := .tail 144 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21022)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 4, 3]], proof := .tail 155 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21023)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 4, 3]], proof := .tail 174 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21024)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 0, 3, 4]], proof := .tail 104 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21025)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 0, 4, 3]], proof := .tail 245 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21026)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 6, 0, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 4, 0, 3]], proof := .tail 40 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21027)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 4, 3, 0]], proof := .tail 140 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21028)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .tail 104 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21029)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 0, 4, 3]], proof := .tail 104 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21030)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 6, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 4, 0, 3]], proof := .tail 185 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21031)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 2, 1, 0, 3, 4]], proof := .low0 (![215, 165, 106, 177, 51, 227, 43, 89, 73, 24, 243, 168, 92, 151, 89, 243, 89, 89, 159, 243, 94, 4, 243, 14, 4, 142, 243, 100]) }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21032)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 2, 1, 0, 4, 3]], proof := .low0 (![21, 34, 60, 177, 51, 227, 43, 96, 219, 24, 243, 168, 4, 101, 37, 243, 37, 37, 159, 243, 94, 4, 243, 14, 4, 142, 243, 100]) }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21033)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 6, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 2, 1, 4, 0, 3]], proof := .low0 (![233, 194, 163, 175, 51, 227, 43, 15, 225, 1, 243, 236, 222, 197, 226, 243, 120, 4, 207, 243, 236, 187, 243, 150, 3, 189, 243, 135]) }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21034)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 6, 4, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 0, 6, 4, 5], ![2, 6, 1, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 2, 4, 1, 0, 3]], proof := .tail 167 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21035)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 6, 4, 2, 5, 0], ![3, 6, 4, 1, 0, 5], ![2, 1, 0, 6, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 2, 1, 0, 3]], proof := .tail 242 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21036)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 4, 3, 0]], proof := .tail 182 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21037)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 2, 1, 4, 3, 0]], proof := .tail 160 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21038)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 6, 4, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 6, 0, 4, 5], ![2, 6, 1, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 2, 4, 1, 3, 0]], proof := .tail 64 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21039)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 6, 4, 2, 5, 0], ![3, 6, 4, 1, 0, 5], ![2, 1, 6, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 2, 1, 3, 0]], proof := .tail 242 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21040)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![6, 3, 4, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 6, 1, 0, 4, 5], ![2, 6, 1, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 2, 4, 3, 1, 0]], proof := .tail 192 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21041)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![6, 3, 4, 2, 5, 0], ![3, 6, 4, 1, 0, 5], ![2, 6, 1, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 242 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21042)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![6, 3, 4, 2, 5, 0], ![6, 3, 4, 1, 0, 5], ![6, 2, 1, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 95 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21043)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 5, 6], ![1, 2, 0, 5, 4, 6], ![1, 2, 0, 5, 3, 6], ![1, 0, 2, 4, 3, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 12 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21044)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 5, 6], ![1, 2, 0, 5, 6, 4], ![1, 2, 0, 5, 6, 3], ![1, 0, 2, 4, 3, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 228 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21045)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 5, 6], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 5, 6, 3], ![1, 0, 2, 4, 6, 3], ![1, 0, 2, 4, 5, 3]], proof := .tail 190 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21046)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 5, 6], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![1, 0, 2, 6, 4, 3], ![1, 0, 2, 5, 4, 3]], proof := .tail 80 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21047)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![1, 0, 6, 2, 4, 3], ![1, 0, 5, 2, 4, 3]], proof := .tail 107 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21048)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 0, 2, 4, 3]], proof := .tail 223 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21049)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 0, 2, 4, 3]], proof := .tail 223 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21050)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 2, 0, 4, 3]], proof := .tail 53 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21051)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 0, 6, 5, 4], ![1, 2, 6, 0, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 2, 4, 0, 3]], proof := .tail 145 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21052)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 0, 6, 5, 4], ![1, 6, 2, 0, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 4, 2, 0, 3]], proof := .tail 86 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21053)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 2, 0, 4, 3]], proof := .tail 53 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21054)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 0, 6, 5, 4], ![1, 2, 6, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 2, 4, 0, 3]], proof := .tail 145 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21055)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 0, 6, 5, 4], ![1, 6, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 4, 2, 0, 3]], proof := .tail 213 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21056)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 0, 6, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 201 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21057)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 6, 0, 5, 4], ![1, 2, 6, 0, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 2, 4, 3, 0]], proof := .tail 47 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21058)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 6, 0, 5, 4], ![1, 6, 2, 0, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 4, 2, 3, 0]], proof := .tail 86 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21059)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 4, 0, 5], ![1, 6, 2, 0, 5, 4], ![1, 6, 2, 0, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 4, 3, 2, 0]], proof := .tail 128 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21060)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 6, 0, 5, 4], ![1, 2, 6, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 2, 4, 3, 0]], proof := .tail 47 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21061)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 6, 0, 5, 4], ![1, 6, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 4, 2, 3, 0]], proof := .tail 213 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21062)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 3, 4, 0, 5], ![1, 6, 2, 0, 5, 4], ![1, 6, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 4, 3, 2, 0]], proof := .tail 119 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21063)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 6, 0, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 25 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21064)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 3, 4, 0, 5], ![1, 6, 2, 0, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 1, 3, 2, 0]], proof := .tail 119 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21065)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 3, 4, 0, 5], ![6, 1, 2, 0, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 3, 1, 2, 0]], proof := .tail 102 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21066)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 3, 4, 0, 5], ![6, 1, 2, 0, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 224 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21067)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 5, 6], ![2, 1, 0, 5, 4, 6], ![1, 2, 0, 5, 3, 6], ![1, 0, 2, 4, 3, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 210 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21068)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 5, 6], ![2, 1, 0, 5, 6, 4], ![1, 2, 0, 5, 6, 3], ![1, 0, 2, 4, 3, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 75 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21069)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 5, 6], ![2, 1, 0, 6, 5, 4], ![1, 2, 0, 5, 6, 3], ![1, 0, 2, 4, 6, 3], ![1, 0, 2, 4, 5, 3]], proof := .tail 123 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21070)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 5, 6], ![2, 1, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![1, 0, 2, 6, 4, 3], ![1, 0, 2, 5, 4, 3]], proof := .tail 112 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21071)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![1, 0, 6, 2, 4, 3], ![1, 0, 5, 2, 4, 3]], proof := .tail 134 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21072)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 0, 2, 4, 3]], proof := .tail 193 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21073)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 0, 2, 4, 3]], proof := .tail 193 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21074)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 2, 0, 4, 3]], proof := .tail 78 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21075)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 2, 0, 4, 3]], proof := .tail 78 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21076)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 0, 6, 5, 4], ![1, 2, 6, 0, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 2, 4, 0, 3]], proof := .tail 103 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21077)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 0, 6, 5, 4], ![1, 6, 2, 0, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 4, 2, 0, 3]], proof := .tail 110 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21078)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 0, 6, 5, 4], ![1, 2, 6, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 2, 4, 0, 3]], proof := .tail 103 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21079)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 0, 6, 5, 4], ![1, 6, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 4, 2, 0, 3]], proof := .tail 87 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21080)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 0, 6, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 78 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21081)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 4, 0, 5], ![2, 1, 0, 6, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 69 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21082)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 6, 0, 5, 4], ![1, 2, 6, 0, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 2, 4, 3, 0]], proof := .tail 103 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21083)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 6, 0, 5, 4], ![1, 6, 2, 0, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 4, 2, 3, 0]], proof := .tail 110 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21084)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 0, 5], ![2, 1, 6, 0, 5, 4], ![1, 2, 6, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 2, 4, 3, 0]], proof := .tail 103 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21085)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 6, 0, 5, 4], ![1, 6, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 4, 2, 3, 0]], proof := .tail 87 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21086)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 4, 0, 5], ![2, 1, 6, 0, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 79 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21087)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 4, 0, 5], ![2, 1, 6, 0, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 69 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21088)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![6, 3, 2, 4, 5, 0], ![3, 6, 1, 4, 0, 5], ![2, 6, 1, 0, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 147 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21089)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![6, 3, 2, 4, 5, 0], ![6, 3, 1, 4, 0, 5], ![6, 2, 1, 0, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 67 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21090)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 5, 6], ![2, 1, 0, 5, 4, 6], ![2, 1, 0, 5, 3, 6], ![1, 0, 2, 4, 3, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 158 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21091)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 5, 6], ![2, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 3], ![1, 0, 2, 4, 3, 6], ![1, 0, 2, 4, 3, 5]], proof := .low6 (![156, 117, 211, 202, 220, 166, 191, 149, 129, 62, 153, 154, 239, 77, 234, 109, 221, 48, 186, 22, 98, 180, 229, 17, 62, 27, 114, 164]) }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21092)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 5, 6], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 5, 6, 3], ![1, 0, 2, 4, 6, 3], ![1, 0, 2, 4, 5, 3]], proof := .tail 241 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21093)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 5, 6], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![1, 0, 2, 6, 4, 3], ![1, 0, 2, 5, 4, 3]], proof := .tail 196 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21094)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![1, 0, 6, 2, 4, 3], ![1, 0, 5, 2, 4, 3]], proof := .tail 42 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21095)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 0, 2, 4, 3]], proof := .tail 42 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21096)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 0, 2, 4, 3]], proof := .low6 (![71, 199, 121, 118, 131, 161, 115, 63, 83, 240, 26, 232, 81, 111, 143, 139, 232, 9, 108, 113, 232, 208, 28, 179, 206, 218, 26, 232]) }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21097)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 2, 0, 4, 3]], proof := .tail 137 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21098)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 2, 0, 4, 3]], proof := .tail 137 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21099)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 2, 1, 0, 4, 3]], proof := .tail 170 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21100)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 6, 0, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 2, 4, 0, 3]], proof := .tail 35 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21101)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 6, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 2, 4, 0, 3]], proof := .tail 35 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21102)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 6, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 2, 1, 4, 0, 3]], proof := .tail 188 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21103)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 6, 4, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 0, 6, 5, 4], ![2, 6, 1, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 2, 4, 1, 0, 3]], proof := .tail 188 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21104)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![3, 6, 4, 2, 5, 0], ![3, 6, 4, 1, 0, 5], ![2, 1, 0, 6, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 132 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21105)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 2, 4, 3, 0]], proof := .tail 35 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21106)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 0, 5], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 2, 4, 3, 0]], proof := .tail 35 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21107)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 2, 1, 4, 3, 0]], proof := .tail 188 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21108)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 6, 4, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 1, 6, 0, 5, 4], ![2, 6, 1, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 2, 4, 1, 3, 0]], proof := .tail 188 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21109)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![3, 6, 4, 2, 5, 0], ![3, 6, 4, 1, 0, 5], ![2, 1, 6, 0, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 242 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21110)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![6, 3, 4, 2, 5, 0], ![3, 4, 6, 1, 0, 5], ![2, 6, 1, 0, 5, 4], ![2, 6, 1, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 2, 4, 3, 1, 0]], proof := .tail 188 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21111)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![6, 3, 4, 2, 5, 0], ![3, 6, 4, 1, 0, 5], ![2, 6, 1, 0, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 242 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21112)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![6, 3, 4, 2, 5, 0], ![6, 3, 4, 1, 0, 5], ![6, 2, 1, 0, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 0 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21113)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 5, 6], ![1, 2, 4, 0, 5, 6], ![1, 2, 3, 0, 5, 6], ![1, 0, 2, 3, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 146 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21114)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 5, 6], ![1, 2, 4, 0, 5, 6], ![1, 2, 3, 0, 6, 5], ![1, 0, 2, 3, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 2 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21115)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 5, 6], ![1, 2, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 3, 4]], proof := .tail 184 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21116)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![4, 3, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 6, 5], ![1, 2, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 3, 4]], proof := .tail 93 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21117)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![4, 3, 2, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 6, 5], ![1, 2, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 3, 4]], proof := .tail 138 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21118)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![4, 3, 2, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 0, 6, 5], ![1, 2, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .tail 138 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21119)) namedLeaf127 = true :=
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

end Jsp404.N4R2ReplayData.LeafShard164
