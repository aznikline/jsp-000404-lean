import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard157
open N4R2RowDataReplay

-- Original cycle 061dfbd8e51f32209bf2880a858cc1d1a26ef13d6b5ceb09b63afbc2fa9e6c54; original global index 505.
def localCycle00000 : Cycle where
  length := 3
  data := {
    node := ![.theta 0, .distance 0 1, .theta 1, .theta 0]
    constant := ![2, -2, 0]
    coefficient := ![1, -1, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 6, .gapUpper 1 6, .thetaNext 0]

-- Original cycle 07acb34ffd5618f2416175e5f8563bf60d8891aa2a7b8695398fcbfdcf5a50c6; original global index 625.
def localCycle00001 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 13 2, .gapLower 6 2, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 07b8132ffc388a0958b5d4522dd86665639924fea75ca4ca2be76edc33124c55; original global index 628.
def localCycle00002 : Cycle where
  length := 5
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .theta 4, .zero]
    constant := ![0, 1, 0, -2, 0]
    coefficient := ![1, 1, 0, -1, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapUpper 4 6, .thetaLower 4]

-- Original cycle 07e0ae0989b19a7bcac541898f245de655841c7d09b82ff1b1388a244f8b2a4b; original global index 637.
def localCycle00003 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 0 4]
    constant := ![2, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 8 2, .triangle 13 1]

-- Original cycle 09c8a95600906d9d4a763eb9da3d4ca1123039ff2692b9fcee6afb722ba60f09; original global index 784.
def localCycle00004 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 0 6, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 11 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 3 6]

-- Original cycle 0c76cefa88b8ad236148f1cbfc10c8bca5ea361acac8b9048cb41ee58a90fe9a; original global index 987.
def localCycle00005 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 12 1, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 0f176a1b6336ef6dcdc8404dc3511d7464e6f921771b30df4f7bbe3570f084e2; original global index 1200.
def localCycle00006 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 6, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 5 0, .triangle 8 2, .gapLower 0 2, .triangle 12 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 11d92d03ae01b17168bb829cf6275965261ca6b81fb8ae9e11bbe03ead8a66ee; original global index 1425.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 28 2, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 11e4881a2d55bc8688ce5268b5f11c44e26f2670964443ac2384aa7cca32531e; original global index 1430.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 6, .distance 0 5, .distance 0 4, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -2, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .gapLower 0 3, .triangle 14 1, .gapLower 0 1, .gapLower 4 3, .triangle 16 1, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 132bea67eaefa723fbfc86b5118ce4c32417bf2d2ea037891a1c2b83d9c3dce2; original global index 1516.
def localCycle00009 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 198167f89cb00062ea7b643477928795050e94d83d486fbb3e38d6ffa338eb47; original global index 1991.
def localCycle00010 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 1, .distance 0 1, .distance 1 3, .distance 3 6, .theta 6, .zero]
    constant := ![0, 3, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 1, .corridorUpper 0 1, .triangle 1 0, .triangle 21 0, .gapLower 6 0, .thetaLower 6]

-- Original cycle 1c87b0eadf9631bf094cef2e44bf9d72197c8d2d6af301e183dfdb5e1b399f60; original global index 2193.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 5 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .gapLower 3 0]

-- Original cycle 21cf3d07895212c9bd598dd00a9b680043b6d2dd65c493cb498d15b24bf95d25; original global index 2593.
def localCycle00012 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle 21fc538dbc30aca0260946a54eca214e53e49825a1ffb4a23247024f4e9a239f; original global index 2599.
def localCycle00013 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -2, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 227c5abf3567114c9257450c42bad3537552bd46a30ebc899d89a20fb2501d63; original global index 2639.
def localCycle00014 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 3 6, .distance 1 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 21 2, .gapLower 6 1, .gapUpper 3 3]

-- Original cycle 2425513bbf6762a5f406c50a3caaa1316ee18b56d62def0c1f9f73084474b789; original global index 2771.
def localCycle00015 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, 0, -2, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 24dd2c1f390a5f2ea7c51dd75b8ea34fdbe810207aea08652630c17f94a6b94f; original global index 2825.
def localCycle00016 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 0 2, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 1, 0, -1, 0, -1, 0, 0, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, true, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .triangle 8 0, .triangle 0 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 26788f88dc66d8061782259edd5b67c8e5980aad6a274bbe0786995e7c6d0a22; original global index 2954.
def localCycle00017 : Cycle where
  length := 4
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .theta 6]
    constant := ![3, -2, 0, -2]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 23 2, .gapLower 6 0]

-- Original cycle 26c09d81e705c60d1649f6c6e63dafabebf41213ac49899d10b13b9b9a3f6550; original global index 2969.
def localCycle00018 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 14 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle 2ab7d75e338b90b1b9a4fd740f227a96848ca33cbc277c4e10c42aef523b7a17; original global index 3249.
def localCycle00019 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.gapUpper 5 4, .gapLower 6 4, .triangle 8 2, .triangle 14 1]

-- Original cycle 2b38fc2115b50c7766f1f1b7300cf28a51037bf1aeabcf8f5036e6a1040f392c; original global index 3300.
def localCycle00020 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 6, .distance 1 6, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -3, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .gapLower 0 3, .triangle 4 1, .triangle 18 1, .triangle 27 1, .triangle 32 1, .corridorLower 3 4]

-- Original cycle 2c83a7ebcc4e4d4cc24cf4ea92bcfd968ec6d012674581be461820f63023c708; original global index 3400.
def localCycle00021 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 6, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .theta 0]
    constant := ![2, -1, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 1 0, .triangle 15 1, .triangle 18 0, .triangle 30 1, .triangle 28 1, .corridorLower 2 4, .thetaNext 1, .thetaNext 0]

-- Original cycle 2eed2c69a3f7f506b730cdde7b18258c5eb1c164f1b5109b02de41dc93cff804; original global index 3590.
def localCycle00022 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 0 2, .distance 0 6, .distance 1 6, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -2, 0, -2, 0, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .triangle 5 1, .gapLower 0 3, .triangle 4 1, .triangle 18 1, .triangle 27 1, .triangle 32 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Original cycle 30406780557f7d32cb80e076280f7ef8fb6cbb40ac2c37e8f191ea50d3c686a4; original global index 3672.
def localCycle00023 : Cycle where
  length := 3
  data := {
    node := ![.theta 0, .distance 0 1, .theta 1, .theta 0]
    constant := ![1, -2, 0]
    coefficient := ![1, -1, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 6, .gapUpper 1 6, .thetaNext 0]

-- Original cycle 339c495ce60265c12f98474b6af3012d33920b9026c9046e12306e8ff4050707; original global index 3949.
def localCycle00024 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 0 5, .distance 0 4]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 4 4, .gapLower 5 4, .gapLower 0 1]

-- Original cycle 35caeaeb4ccd789c35f8d3d4d9c196ffee4a2b04a375a393ac6e32ded3a8473c; original global index 4125.
def localCycle00025 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![4, -2, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.gapLower 2 6, .gapLower 6 2, .gapLower 6 1, .triangle 18 1, .triangle 17 0, .triangle 28 1, .corridorLower 2 4]

-- Original cycle 368cef6b6c978ae6a572ee7576e57fdef664f10e4ef2c2f4a4957b08220b923a; original global index 4188.
def localCycle00026 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 3 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 29 2, .gapLower 6 3, .triangle 4 1, .triangle 21 1, .gapLower 6 0]

-- Original cycle 393f5dce4c35096d60baa06bd8dfa71374b39ca36f6518231c17a82160d4651c; original global index 4404.
def localCycle00027 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 4 6, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 34 1]

-- Original cycle 3be59515d9155bfa265d754599c61d68c506714530308ba8f9e53354be8925be; original global index 4640.
def localCycle00028 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 0 6, .distance 0 5, .distance 0 4]
    constant := ![2, 0, -2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 4 4, .triangle 13 2, .gapLower 0 2, .gapLower 0 1]

-- Original cycle 3d93ac90057f6c0f8bfb0725d45b5410e6ac949eac5d595b019cc977928d7858; original global index 4767.
def localCycle00029 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 8 2, .gapLower 6 1, .gapLower 6 0]

-- Original cycle 3da3cab1071a8753d703155c1871305a5cb541ef2da61db692befcc0f4476fa1; original global index 4773.
def localCycle00030 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, -3, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 27 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 3daaf86528d7f60fecc402848d919f39a5c01cdc9529167e26f84d1b5849672e; original global index 4776.
def localCycle00031 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 14 0, .triangle 12 1]

-- Original cycle 4051b26f8eaee4e890b98be01344f5a78859841069f05d40a6a3e2acc405bb5c; original global index 4971.
def localCycle00032 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 4060629676aa43dfa6e4bd5531a2c3cc17bb86d6aeab47273307c6cb103dad85; original global index 4978.
def localCycle00033 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 12 1, .triangle 13 0, .triangle 23 2, .triangle 24 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle 425b8fb35c5eecefbb02bd82b4f52ac28287b8c2bf3b94fa2ccc8f3a11f5e443; original global index 5112.
def localCycle00034 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 26 1, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 3 4]

-- Original cycle 44c403fba076fd7fdcc8c56601a348e8496fc9cfc54050a82067c18e71c72d92; original global index 5329.
def localCycle00035 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 459072b78f61275c5ac33ceac24d49890c139bf72a27a228da009f08dc87dc66; original global index 5381.
def localCycle00036 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 26 1, .triangle 31 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 45dd50adf6af8d21d36a2d246eef6634fb58a323c51610f57b8e5ecbbdc3a34f; original global index 5403.
def localCycle00037 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -2, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 466e36c7f75e4496b1e9b13f38df4a29c9ff66d3c5527c3025e1b41e2b31706f; original global index 5448.
def localCycle00038 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 2, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 3, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 4696b7b94e11db6e75e0a89597727fbdd29c11b4332f86270c1517fec5c8a4bb; original global index 5460.
def localCycle00039 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 15 1, .triangle 17 2, .triangle 22 1, .triangle 23 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Original cycle 470acbd4d8d7c6937557b75fb19108fbe8dff76abd0487f2656a32fc2f9811b2; original global index 5508.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 3 4]

-- Original cycle 491ad06b417219a28230979c78ab1ed3851a87d716b9409276862f7e841a2e27; original global index 5661.
def localCycle00041 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .gapLower 6 3, .triangle 4 1, .triangle 18 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 4ac89ddeb1f17182d1e1e3181fbb040d40130cb064c177a511711471d490b809; original global index 5802.
def localCycle00042 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 13 2, .gapLower 6 1, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 4d05181d77dff10552d177146cb394277a418e2d61fa8ab98d05e47f0967ecf6; original global index 5983.
def localCycle00043 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 2, .triangle 13 1, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 4d859de56830824c6eb6ea57cd2d30c6fc6c107ff8728a204fdc1e525f9d8712; original global index 6018.
def localCycle00044 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 1 1, .triangle 15 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle 4dd8c51d80b54966fff152494e77de4d5126da8332a0b2540392a97603ceb2cf; original global index 6043.
def localCycle00045 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 29 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 4ffd4abef0869249c7f10937bca1fc182d80549801972c899b9fbebaf020f4c4; original global index 6212.
def localCycle00046 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 14 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle 54422e54060374a9b71daec6c22418471a07c59378730bb29146703cfdeea0f4; original global index 6528.
def localCycle00047 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![4, -2, -2, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true, false] }
  origin := ![.gapLower 3 6, .gapLower 6 3, .gapLower 6 2, .triangle 4 1, .triangle 18 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle 56436e09987eb884487751841a5e0f11b288fed521d4a8255391c682632decd9; original global index 6688.
def localCycle00048 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 18 2, .gapLower 6 0]

-- Original cycle 56826de6a2d647295ac60d12770427400ab28e1a8738f889d9db143254c532ab; original global index 6707.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 3 4]

-- Original cycle 5683785bcd7e52d71523842345072cb917423f9a06a93ee41af549c963921dc4; original global index 6708.
def localCycle00050 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 12 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 571e8adc6f5027a4130092d53eb6bc38bca596df09862aee8a6940dbd87a463e; original global index 6752.
def localCycle00051 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 5 4, .triangle 14 2, .gapLower 0 2]

-- Original cycle 579ee1a59ea3c017dae3bbbbb5988ee15b03f654535bf06d886041e224beb27f; original global index 6800.
def localCycle00052 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 2 5, .gapLower 3 5, .gapLower 0 4]

-- Original cycle 590fe57ad3d916a8f1fcc9bfe5fe77a853a2376e5bad5ac80a8e7f9b482b9587; original global index 6904.
def localCycle00053 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2]
    constant := ![0, 0, 2, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, true, false, false] }
  origin := ![.triangle 6 2, .triangle 12 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0]

-- Original cycle 5a44bf134757bd85e0d0a4f53e2461d511431a13bc7a91aa346f0a99418bfdea; original global index 7023.
def localCycle00054 : Cycle where
  length := 5
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .theta 4, .zero]
    constant := ![0, 2, -2, -2, 0]
    coefficient := ![1, 1, 0, -1, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .gapUpper 4 6, .thetaLower 4]

-- Original cycle 5b3a9ca9b2ee90864fc2011d7968d0fb7a373a3e8260c34bca325d6d033720ba; original global index 7100.
def localCycle00055 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 6, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 2, .triangle 8 0, .triangle 7 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 5de17d299e58a6bd4db63a2ac7a8ff30ed8ae59dbbf6f20c09fcbfa055c744f2; original global index 7302.
def localCycle00056 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 2 6, .distance 2 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 5, .gapLower 6 3, .triangle 27 1]

-- Original cycle 5fb75ae5a2f0e7499476b05c28a816c8468812a29be082991ff5da0a00217265; original global index 7455.
def localCycle00057 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 6, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 5 0, .gapLower 0 3, .triangle 14 1, .triangle 12 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 617b640bcd528b891f999f83cf4fdb669b1f2bd0e968581ff29536ff8f3799fe; original global index 7602.
def localCycle00058 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 21 0, .gapLower 1 3, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Original cycle 621f42ffbcf16e985659c5e29f34350e88aed8bf29bfbc2c41c3295e51dfff97; original global index 7660.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 6, .distance 0 5, .distance 1 5, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -3, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 2, .gapLower 0 2, .triangle 3 1, .triangle 17 1, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle 64798178bbf59775b21d7cdca909a3829b71bf9d9b99e57bc033df0d39106b88; original global index 7827.
def localCycle00060 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 29 2, .triangle 30 1, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 6714af4fe69cfc4881eb00fa8d9be0caa66597b472faffeadb39cff206468886; original global index 8010.
def localCycle00061 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 0 1]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 5, .gapLower 3 4, .gapUpper 1 5]

-- Original cycle 6aeb13386841f15265c830c09d9d181224e7bb2fb1afc53bd59d2d817a4047c9; original global index 8327.
def localCycle00062 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 28 2, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 6bae818d7c0862d21171142bca8bdee96755b83a16397132a08be53e25d9bc5c; original global index 8380.
def localCycle00063 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 29 2, .gapLower 6 3, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 6be58fe150286db5af7e3cce0cfd22a0f3e254aecd8695871c3dc23fa476c41c; original global index 8406.
def localCycle00064 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, 0, 0, -2, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .triangle 8 2, .gapLower 6 2, .triangle 18 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 6bebebbebd6418d5dde3823b6e81a452999955b65fc30c5825543670debe1cad; original global index 8411.
def localCycle00065 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 30 2, .gapLower 6 3, .triangle 4 1, .triangle 21 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 6e1428f7e0b5d487d460574ac932cdab6361215269e22476ac9bf5ac96f22373; original global index 8547.
def localCycle00066 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 7 2, .gapUpper 5 4, .gapLower 6 4, .triangle 8 0]

-- Original cycle 73e05e10dc84f836dcc62218478779c51de4b9c6e7f5c3600bd46a5c7df25829; original global index 8987.
def localCycle00067 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 7cb068a466218d4a4f9001873f1f51256d128ded9e592ad9c49e9ac3db9cc5fa; original global index 9656.
def localCycle00068 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 3 6, .distance 1 3]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 21 2, .gapLower 6 1, .gapUpper 3 3]

-- Original cycle 7cde13c092c9690a94a16c7edd1e9be61be42bb7cf8453143cba16095aca8644; original global index 9671.
def localCycle00069 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, 0, 0, 0, -2, 0, 0, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .gapLower 6 2, .triangle 4 1, .triangle 21 1, .triangle 15 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 7db7f6545a2da481fab61a5ccea28a075dca59adf2efd741c4ca82ba643ab7c5; original global index 9758.
def localCycle00070 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle 7e288f5d32c0a54ce241fa1715457a1638716314ce592bcab7958d66e0718e90; original global index 9801.
def localCycle00071 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 4 2, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle 7e5d957ad83f3c6f02f128e1b2635929dd11d7d36129e51e1e41c4fc6fffc1b1; original global index 9815.
def localCycle00072 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 0 6, .distance 0 2]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 4, .gapLower 6 3, .triangle 8 1]

-- Original cycle 7f77e5815cf57931e238fe036f338113e8a4b1d726a40087d66f11dc34aafe25; original global index 9886.
def localCycle00073 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5, .theta 5]
    constant := ![3, -1, -2, 0, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 8 2, .gapLower 6 2, .triangle 18 1, .triangle 17 0, .triangle 26 1, .gapLower 5 0]

-- Original cycle 820becf8ab0cb415cc68072e35c2db2fc97e3ced29e3a0f8b6895c820af0e289; original global index 10096.
def localCycle00074 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 27 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 83e9460b4c32df83c11139502a9dc2b6452c53aa09bce851c657c7e79b45210d; original global index 10240.
def localCycle00075 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .theta 5]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 26 1, .gapLower 5 0]

-- Original cycle 84ba9d6a94860ddc5e94c9d55ffbb00db2623c1ccc2cfbcac5c255ac82e5ce42; original global index 10305.
def localCycle00076 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 0 2, .distance 0 6, .distance 0 5, .distance 1 5, .theta 1]
    constant := ![3, -2, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .triangle 5 1, .triangle 8 2, .gapLower 0 2, .gapLower 5 3, .corridorLower 1 5]

-- Original cycle 8846baf5eb64f3234d2ccd4aad37d1b132227641ef9598ace6537b47ca738ac2; original global index 10561.
def localCycle00077 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -1, 0, -1, 0, 0, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 1 0, .triangle 15 1, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 897864a48b3c0a0ab0e9f5db5b00bf566191ab6631bdd90889bde680260954ec; original global index 10641.
def localCycle00078 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 12 1, .triangle 13 0, .triangle 34 1, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 8a8155cec16cb07cf04ca6f63f8cd0ce720968edbac612895af5915b4f474f19; original global index 10729.
def localCycle00079 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 4, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 17 0, .triangle 16 0, .corridorLower 2 4, .thetaLower 2]

-- Original cycle 8ac6cb49822e0f08c547c10ec675b0bca61f1e7b8e9050fe2724fc3d8fa8f81f; original global index 10752.
def localCycle00080 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 27 2, .gapLower 6 2, .triangle 8 1, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 92423a0eb35fbf9045dc963a750726440be37509300c91cfb0d81872aac9ce2c; original global index 11329.
def localCycle00081 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .triangle 12 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 9350e2157b4c7950652db12d46426a9748b7d5d89e7a9d05f39b9e0e69e16e01; original global index 11423.
def localCycle00082 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 23 2, .gapLower 6 1, .corridorLower 3 6, .thetaLower 3]

-- Original cycle 9aec3a91dd5fa6df76cd9c4dd30f224655b25ff6a56c007862dbc57c0b81708b; original global index 12042.
def localCycle00083 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 22 2, .triangle 24 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle 9b008ea9711e671b10a76eece41f5035f7833daf0e9282580f45b7dcc0711a92; original global index 12047.
def localCycle00084 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 8 2, .triangle 11 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 9da6dfec8384cfc8069b1b10bf7a55a3abb8b8fa8fe352a6c59e2f4bba1a1427; original global index 12263.
def localCycle00085 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 3 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 8 2, .triangle 11 1, .gapLower 6 0]

-- Original cycle a13c004e7091ceed617b6582ed7bb2f0550c1975fe4f44d40abf641c8219687b; original global index 12535.
def localCycle00086 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 0 6, .distance 0 5, .distance 0 4]
    constant := ![2, 0, 0, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, true, false] }
  origin := ![.gapUpper 4 4, .triangle 13 2, .triangle 14 1, .gapLower 0 1]

-- Original cycle a4facf6a6b9fb2219f2a147b0850b70b8c2d0a1bf379b42abf740a295393f5f7; original global index 12822.
def localCycle00087 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 0 6, .distance 1 6, .theta 1]
    constant := ![3, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 11 2, .gapLower 6 2, .corridorLower 1 6]

-- Original cycle a79ed8c6bb525e72fa21057a7a42e04f04345030e4ad07dad773325f9e2b9b98; original global index 13045.
def localCycle00088 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -2, -2, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 2, .gapLower 6 3, .gapLower 6 2, .triangle 18 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle a9ede89c23816e448cde85c068870f85c8fa6add3778f886779b6b4b9c826da5; original global index 13228.
def localCycle00089 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .corridorLower 3 6]

-- Original cycle ac04c244e9685d8b2305719fd5c63c1a23cf29b03ebb4e280e400f575bfe981e; original global index 13406.
def localCycle00090 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle ad3778764584572b287166f736ffa23746b74240c0e708eebe4b8bf899d8f5fa; original global index 13504.
def localCycle00091 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 3 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 29 2, .triangle 8 2, .gapLower 6 2, .triangle 21 1, .gapLower 6 0]

-- Original cycle ae43c9700e9af830336c85fc4948782c28ae65cea8171b2ae22978ff09be3910; original global index 13598.
def localCycle00092 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle af0d6e9717ad64d30d3c037f28f7017d827030706c2e7ec10522896a9d2196ca; original global index 13666.
def localCycle00093 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .gapLower 6 2, .triangle 4 1, .gapLower 6 0]

-- Original cycle af30d4f7ed507300f010360836b8884231b7151196f6eb0154f7d87cca58149c; original global index 13685.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 29 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle b0c92015af8ca5b5835da53934969d6db292e8112bb46aa89f838504e4d851cb; original global index 13806.
def localCycle00095 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle b12877025c95a4dceeb42005e2f8ec4c2b2fb9bcaf9aa5a29d563b4524aa6d6a; original global index 13836.
def localCycle00096 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 0 6, .thetaLower 0]

-- Original cycle b160e60b1ea71441e28113946efafdf3e54a30630dbf4428aaf019e2aa5d0c0c; original global index 13858.
def localCycle00097 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -3, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 11 2, .gapLower 6 2, .triangle 18 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Original cycle b1a7861e582ba5a98691db35a67b12438f01284d1054431388d7f57a76f838f1; original global index 13882.
def localCycle00098 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle b2bc98eb1c01a1a12b81a8dbe85bbf8a28481d2ea72884115fb9b6f431dc501e; original global index 13971.
def localCycle00099 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 30 1, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle b61c86a100352068b0cd9df469511ac313cc3e81934b8bae2b51d3cadfea015a; original global index 14223.
def localCycle00100 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -3, 0, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .gapLower 6 2, .triangle 4 1, .triangle 18 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle b66c0d9b8cc51f0048bfc1449270634804d78a7dbe1bc1f7f918b018be713e43; original global index 14258.
def localCycle00101 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 3 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -2, 0, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 21 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Original cycle ba3ba3a64bd4d277e68ded9e54bc6d2d1735387cb0d7f87d9315e48a905c3622; original global index 14540.
def localCycle00102 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 3 6, .theta 6]
    constant := ![3, 0, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 29 2, .triangle 8 2, .triangle 4 1, .gapLower 6 1, .gapLower 6 0]

-- Original cycle bb351d7cae1391b3f3655a05988514cdaa629f48af003907a6936a97b43a6db6; original global index 14617.
def localCycle00103 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4]

-- Original cycle bbad4a25dfd623b0f1a77633880b7dfea3638013c62e3d724018136cf533788a; original global index 14653.
def localCycle00104 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 4 4, .triangle 34 1, .triangle 14 0, .gapLower 0 1]

-- Original cycle bd9c216afffb7a72fa221a2ffa54e0051c0ea870acc97880dab7a83b86ed5ee6; original global index 14790.
def localCycle00105 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 0 4]
    constant := ![2, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 30 2, .gapLower 6 3, .triangle 13 1]

-- Original cycle bf2e0d424cfa7f19f2ea65141a41b49e860aa74e0ae743956d52c8a67956e08d; original global index 14919.
def localCycle00106 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 17 0, .gapLower 1 2, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle bfe6eb6025d022e2274ce332a2c96bc9285b0757c040327dbc8947ad02d07297; original global index 14973.
def localCycle00107 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 14 2, .gapLower 6 2, .triangle 21 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle c161896ee3bc05da95f0c3dba2b6936d5b32a5508cd06b60a3e7516277ef5d00; original global index 15100.
def localCycle00108 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 2, .triangle 13 1, .triangle 12 0, .triangle 28 2, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle c178933806751a3e88395a49cb77830b3d2a136e33ebca2dd2f315246f2e38aa; original global index 15107.
def localCycle00109 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 1 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -2, 0, 0, -1, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .gapLower 3 4, .triangle 15 1, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Original cycle c187371c8b5a0569f6bd73f5e9014194766667b03bfe4e5c4b37284a93601c62; original global index 15115.
def localCycle00110 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle c1d339d13370200fe12f6f0903b1d5bc3834a60f89039b7c6a9321ed9d70c905; original global index 15134.
def localCycle00111 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 28 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 3 4]

-- Original cycle c3087983818f9d947d3a977806ca423f44d35c6992897acbceaa11c10a61400f; original global index 15223.
def localCycle00112 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 6, .distance 0 5, .distance 1 5, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -2, -2, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .gapLower 0 3, .gapLower 0 2, .gapLower 5 3, .triangle 17 1, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle c4be1fbd3e921fe58278e462356479e9dffcfd64d8c5ed956acc27e81cf5827f; original global index 15344.
def localCycle00113 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 1 6, .distance 1 3, .distance 1 2, .distance 2 5, .distance 2 4, .theta 2, .theta 1]
    constant := ![3, 0, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 2, .gapLower 6 1, .triangle 21 1, .triangle 15 1, .triangle 17 0, .triangle 28 1, .corridorLower 2 4, .thetaNext 1]

-- Original cycle c60faa0d9d01e952cbc17b216106cb45009a9fc2c92f0bc0e70459bb2603089e; original global index 15447.
def localCycle00114 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 28 1, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle c9775d2134d5cc16c90a5ad1d8ab53f2c004577548025fb8942c1a98c82561e7; original global index 15749.
def localCycle00115 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 30 0, .triangle 33 0, .triangle 20 0, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle cc305c9383d06821940b9f329d0586a982b4736c6ac3a71f41c50f4cb7e7e9ee; original global index 15963.
def localCycle00116 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 2, .triangle 18 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle cd05bdc16dd563b0a8f0aa3685cca8bdb2e816b2ca5d79300b5b539aac502a9b; original global index 16022.
def localCycle00117 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 32 2, .gapLower 6 3, .gapUpper 2 6, .thetaLower 2]

-- Original cycle cfa70458c02f4dfba3cbecff02efec089c0c613449c33b2af9c56e03e0e5cb2a; original global index 16205.
def localCycle00118 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 3, .triangle 4 1, .triangle 18 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle cfefc7202565f44e8eb07ee2589b1dc617b927b95eb3b6610668d1c755fb725f; original global index 16228.
def localCycle00119 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle d047ef051dda738469947dfb81fe8bfdc7e768fc2046c9df0b0845a344ace9d9; original global index 16256.
def localCycle00120 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 28 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .corridorLower 3 6]

-- Original cycle d2556b604a680542f8a45a3a4e466fb23f1fa04809e08dce0a2af98a5eaa2caa; original global index 16410.
def localCycle00121 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle d2e119f1153e09b64f0e5aa799ece546a0fbba5329f02567e4275f2637f50b9d; original global index 16451.
def localCycle00122 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle d3aeaef08bdd9470a98132b71b73d6b326ed20cc7c6be18ef8159ee48a928379; original global index 16518.
def localCycle00123 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 3 6, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .theta 1]
    constant := ![3, -1, -1, -2, 2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 21 0, .gapLower 6 0, .gapLower 6 6, .triangle 34 0, .triangle 22 0, .corridorLower 1 4]

-- Original cycle d6627eefb1da1630a83daba0bb1a5b5f14f274b442dcef1a37da11ff808cfc4b; original global index 16738.
def localCycle00124 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 3 6, .theta 6, .distance 5 6, .distance 4 6, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -2, 3, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 1, 0, -1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 21 0, .gapLower 6 0, .corridorUpper 5 6, .gapLower 6 5, .gapUpper 4 6, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Original cycle d75a72d4007c38011615086d5d2cd92357a832811497abef08c39dabd3f8bc4e; original global index 16809.
def localCycle00125 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 0 5]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 5 4, .gapLower 6 4, .gapLower 6 3, .triangle 14 1]

-- Original cycle dce2becb9e5415d0398c67b7869a0bf279800fcdaf0238f235e56aeed67c7e59; original global index 17264.
def localCycle00126 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 29 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle dde95c7a9ed71df9846a779f168c072c4af816a06def98d4e526bb6ce1171404; original global index 17349.
def localCycle00127 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![4, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .triangle 29 0, .gapLower 2 0]

-- Original cycle e1a2948ae2190a6d5228bb6dd8f0b6c86ab6f896431a52860a269762b561ddad; original global index 17643.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, 0, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 30 2, .triangle 8 2, .triangle 4 1, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle e26642ec7804dcd6bf03bb1a4264b2b08c35d84d78075518dfffbe58f37bdc36; original global index 17702.
def localCycle00129 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 12 1, .triangle 13 0, .triangle 29 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle e574cd36d4633bcc183119876d7115d489d28a81e8b06875aafd46123f2942d4; original global index 17943.
def localCycle00130 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 2 4, .theta 2, .theta 1]
    constant := ![3, 0, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 11 2, .gapLower 6 2, .triangle 18 1, .triangle 17 0, .triangle 28 1, .corridorLower 2 4, .thetaNext 1]

-- Original cycle e5c343a89ca375f49f50680b40975ec45ea82c2b2382b509673fa15ce2d94e6b; original global index 17975.
def localCycle00131 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 0 6, .distance 1 6, .distance 3 6, .theta 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 11 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 3 6, .thetaNext 2, .thetaNext 1]

-- Original cycle e6315703f428c2348103c116417011f7517f8f8b35fc8dcc1c56a0d47167f61a; original global index 18014.
def localCycle00132 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 6, .distance 0 5, .distance 0 4, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 2, .gapLower 0 2, .gapLower 0 1, .gapLower 4 3, .triangle 16 1, .triangle 25 1, .corridorLower 3 4]

-- Original cycle e6c1a80fd72d56d0e98eb070b3bf36791fc1ace73ddfc44cf264e0ef9d78c5f7; original global index 18050.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 14 0, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle e9553d27e748575cbd6470cd6aacf023a3137722954313c109258347f9f8400f; original global index 18236.
def localCycle00134 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 14 0, .triangle 12 1]

-- Original cycle eac5952cb3cde7a4227bfae468a36cfc57e3ba2986d8f50e5a0fc908325d3c83; original global index 18338.
def localCycle00135 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 26 1, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle ee52c2152b45bee9b081f67ee5c3cfd14900672a27ab04eebb96d44713209521; original global index 18601.
def localCycle00136 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -3, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle efc72cf2ab83c9018d6615117e65c70a31e3c3a10ab2a179d4faa991e5c8c402; original global index 18706.
def localCycle00137 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .triangle 32 0, .gapLower 3 0]

-- Original cycle f0a5ec230185e4019254edcae8fe7514cfdaaae8699fbaefbd7e5d4d1742afef; original global index 18766.
def localCycle00138 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 2 5, .gapLower 3 5, .gapLower 0 4]

-- Original cycle f0dd3ef9e1e286c86b7f07c3c7d67a4927e57fc525b97299e60c269ce5be9ce1; original global index 18786.
def localCycle00139 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, -2, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .gapUpper 2 6, .thetaLower 2]

-- Original cycle f11d57b35b9075727a9595bb58fa33d9e93b7a39482939d595f772cd3153e21f; original global index 18807.
def localCycle00140 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 0 5, .distance 0 4]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 4 4, .gapLower 5 4, .gapLower 0 1]

-- Original cycle f4adcf7d6e389e60097b67ef9b038fccc6aa591c5f166161eb823681a0e8fa3e; original global index 19074.
def localCycle00141 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 2, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 8 0, .triangle 0 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle f531314df55f2ab86cfe62b046608704fa3e71631f68cb8beb3b58a19d2d9bbb; original global index 19113.
def localCycle00142 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -3, 3, 0, 0, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Original cycle f55b4d8bb43f55f5c69ab1546c1669309c6355e9764a522fbb2e4ef31a687358; original global index 19129.
def localCycle00143 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![4, -2, 0, -2, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.gapLower 3 6, .gapLower 6 3, .triangle 8 2, .gapLower 6 1, .triangle 18 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle f6932edebc44b4b342c14a5df68eb1cf0ee0778c95206066e150ab1e891d3597; original global index 19238.
def localCycle00144 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .distance 2 6, .distance 2 5, .distance 2 4, .theta 2, .theta 1]
    constant := ![3, -2, -2, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .gapLower 0 4, .gapLower 2 4, .triangle 18 0, .triangle 30 1, .triangle 28 1, .corridorLower 2 4, .thetaNext 1]

-- Original cycle f873549cbbea893b218f0f40b4af3d04418c5368dc985b1b7f448ab1a91b64f5; original global index 19378.
def localCycle00145 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle fab2edc80983ccb78e8fa946fdb266104563ed60aab5b08f557f8d908e9580d4; original global index 19560.
def localCycle00146 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 28 2, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle fbc2d896985eb067d0b26beaa608725382a1f9974c9cc64f5d59a529b1b1e807; original global index 19656.
def localCycle00147 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 6, .distance 0 6, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 2, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .corridorLower 3 6]

-- Original cycle fd764a73dfdf35d972efa3774617fe6f6120537b30244c33bab0b700237bc1c9; original global index 19810.
def localCycle00148 : Cycle where
  length := 12
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 3, .distance 1 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true, false, true, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .gapLower 3 4, .triangle 15 1, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle ff017b8f825449d2a05eefa38c3f4cfc3e716a42c4e671521b973898050b2a9f; original global index 19937.
def localCycle00149 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 15 1, .triangle 17 2, .triangle 24 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

def library : Library := fun id => if id < 75 then (if id < 37 then (if id < 18 then (if id < 9 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))))) else (if id < 13 then (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none))) else (if id < 15 then (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))))) else (if id < 27 then (if id < 22 then (if id < 20 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none))) else (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none))))) else (if id < 32 then (if id < 29 then (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none)) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)))) else (if id < 34 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))))))) else (if id < 56 then (if id < 46 then (if id < 41 then (if id < 39 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))) else (if id < 43 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))))) else (if id < 51 then (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none)))) else (if id < 53 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)))))) else (if id < 65 then (if id < 60 then (if id < 58 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 62 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none)) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none))))) else (if id < 70 then (if id < 67 then (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)))) else (if id < 72 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)))))))) else (if id < 112 then (if id < 93 then (if id < 84 then (if id < 79 then (if id < 77 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none))) else (if id < 81 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none))))) else (if id < 88 then (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none))) else (if id < 90 then (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none)))))) else (if id < 102 then (if id < 97 then (if id < 95 then (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none))) else (if id < 99 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none))))) else (if id < 107 then (if id < 104 then (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none)) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)))) else (if id < 109 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none))))))) else (if id < 131 then (if id < 121 then (if id < 116 then (if id < 114 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none))) else (if id < 118 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none)) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none))))) else (if id < 126 then (if id < 123 then (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none)) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none)))) else (if id < 128 then (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)))))) else (if id < 140 then (if id < 135 then (if id < 133 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none)) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none))) else (if id < 137 then (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none))))) else (if id < 145 then (if id < 142 then (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none)) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none)))) else (if id < 147 then (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none)) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![4, 6, 5, 2, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 6, 0, 3], ![4, 1, 5, 6, 0, 2], ![3, 2, 1, 0, 6, 5], ![1, 3, 2, 6, 0, 4], ![1, 3, 2, 5, 0, 4]], proof := .tail 133 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20096)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![4, 6, 5, 2, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 5, 0, 3], ![4, 1, 5, 6, 0, 2], ![3, 2, 1, 0, 6, 5], ![1, 3, 6, 2, 0, 4], ![1, 3, 5, 2, 0, 4]], proof := .tail 115 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20097)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![4, 6, 5, 2, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 5, 0, 3], ![4, 1, 6, 5, 0, 2], ![3, 2, 1, 0, 6, 5], ![1, 6, 3, 2, 0, 4], ![1, 5, 3, 2, 0, 4]], proof := .tail 9 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20098)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![4, 6, 5, 2, 3, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 6, 5, 0, 3], ![4, 1, 6, 5, 0, 2], ![3, 2, 1, 0, 6, 5], ![6, 1, 3, 2, 0, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 9 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20099)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![4, 6, 5, 2, 3, 1], ![4, 2, 6, 3, 5, 0], ![4, 1, 6, 5, 0, 3], ![4, 6, 1, 5, 0, 2], ![3, 2, 1, 0, 6, 5], ![6, 1, 3, 2, 0, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 34 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20100)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![4, 6, 5, 2, 3, 1], ![4, 6, 2, 3, 5, 0], ![4, 6, 1, 5, 0, 3], ![4, 6, 1, 5, 0, 2], ![3, 2, 1, 0, 6, 5], ![6, 1, 3, 2, 0, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 49 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20101)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 6, 0, 3], ![4, 1, 5, 6, 0, 2], ![3, 2, 1, 6, 0, 5], ![1, 3, 2, 6, 0, 4], ![1, 3, 2, 5, 4, 0]], proof := .tail 78 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20102)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 5, 0, 3], ![4, 1, 5, 6, 0, 2], ![3, 2, 1, 6, 0, 5], ![1, 3, 6, 2, 0, 4], ![1, 3, 5, 2, 4, 0]], proof := .tail 115 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20103)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 5, 0, 3], ![4, 1, 6, 5, 0, 2], ![3, 2, 1, 6, 0, 5], ![1, 6, 3, 2, 0, 4], ![1, 5, 3, 2, 4, 0]], proof := .tail 9 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20104)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 6, 5, 0, 3], ![4, 1, 6, 5, 0, 2], ![3, 2, 1, 6, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 9 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20105)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![4, 2, 6, 3, 5, 0], ![4, 1, 6, 5, 0, 3], ![4, 6, 1, 5, 0, 2], ![3, 2, 1, 6, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 34 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20106)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![4, 6, 2, 3, 5, 0], ![4, 6, 1, 5, 0, 3], ![4, 6, 1, 5, 0, 2], ![3, 2, 1, 6, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 49 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20107)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![6, 4, 2, 3, 5, 0], ![4, 6, 1, 5, 0, 3], ![4, 6, 1, 5, 0, 2], ![3, 2, 6, 1, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 106 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20108)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![6, 4, 2, 3, 5, 0], ![6, 4, 1, 5, 0, 3], ![4, 6, 1, 5, 0, 2], ![3, 6, 2, 1, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 11 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20109)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![6, 4, 2, 3, 5, 0], ![6, 4, 1, 5, 0, 3], ![6, 4, 1, 5, 0, 2], ![6, 3, 2, 1, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 89 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20110)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![4, 5, 2, 3, 6, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 0, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 2, 1, 0, 5, 6], ![3, 1, 2, 0, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 98 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20111)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![4, 5, 2, 3, 6, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 0, 6, 3], ![4, 5, 1, 0, 6, 2], ![3, 2, 1, 0, 5, 6], ![3, 1, 2, 0, 4, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 9 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20112)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![4, 5, 2, 6, 3, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 0, 6, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 0, 5, 6], ![3, 1, 2, 0, 4, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 55 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20113)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![4, 5, 2, 6, 3, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 5, 0, 6, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 5, 6], ![3, 1, 2, 0, 4, 6], ![3, 1, 0, 2, 4, 5]], proof := .tail 55 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20114)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![4, 5, 2, 3, 6, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 0, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 2, 1, 0, 6, 5], ![3, 1, 2, 0, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 121 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20115)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![4, 5, 2, 3, 6, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 0, 6, 3], ![4, 5, 1, 0, 6, 2], ![3, 2, 1, 0, 6, 5], ![3, 1, 2, 0, 6, 4], ![1, 0, 3, 2, 5, 4]], proof := .tail 9 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20116)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![4, 5, 2, 6, 3, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 0, 6, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 1, 2, 0, 6, 4], ![1, 3, 0, 2, 5, 4]], proof := .tail 79 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20117)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![4, 5, 2, 6, 3, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 5, 0, 6, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 1, 2, 0, 6, 4], ![3, 1, 0, 2, 5, 4]], proof := .tail 79 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20118)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![4, 5, 6, 2, 3, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 6, 0, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 0, 5, 6], ![3, 1, 2, 0, 4, 6], ![1, 3, 2, 0, 4, 5]], proof := .tail 99 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20119)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![4, 5, 6, 2, 3, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 6, 0, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 1, 2, 0, 6, 4], ![1, 3, 2, 0, 5, 4]], proof := .tail 99 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20120)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![4, 6, 5, 2, 3, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 6, 0, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 1, 2, 6, 0, 4], ![1, 3, 2, 5, 0, 4]], proof := .tail 133 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20121)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![4, 6, 5, 2, 3, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 6, 5, 0, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 1, 6, 2, 0, 4], ![1, 3, 5, 2, 0, 4]], proof := .tail 92 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20122)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![4, 5, 6, 2, 3, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 5, 6, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 5, 6], ![3, 1, 2, 0, 4, 6], ![3, 1, 2, 0, 4, 5]], proof := .tail 99 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20123)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![4, 5, 6, 2, 3, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 5, 6, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 1, 2, 0, 6, 4], ![3, 1, 2, 0, 5, 4]], proof := .tail 99 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20124)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![4, 6, 5, 2, 3, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 5, 6, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 1, 2, 6, 0, 4], ![3, 1, 2, 5, 0, 4]], proof := .tail 133 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20125)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![4, 6, 5, 2, 3, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 6, 5, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 1, 6, 2, 0, 4], ![3, 1, 5, 2, 0, 4]], proof := .tail 92 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20126)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![4, 6, 5, 2, 3, 1], ![4, 2, 6, 5, 3, 0], ![4, 1, 6, 5, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 6, 1, 2, 0, 4], ![3, 5, 1, 2, 0, 4]], proof := .tail 70 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20127)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![4, 6, 5, 2, 3, 1], ![4, 2, 6, 5, 3, 0], ![4, 1, 6, 5, 0, 3], ![4, 6, 5, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![6, 3, 1, 2, 0, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 9 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20128)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![4, 6, 5, 2, 3, 1], ![4, 6, 2, 5, 3, 0], ![4, 6, 1, 5, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 6, 1, 2, 0, 4], ![3, 5, 2, 1, 0, 4]], proof := .tail 90 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20129)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![4, 6, 5, 2, 3, 1], ![4, 6, 2, 5, 3, 0], ![4, 6, 1, 5, 0, 3], ![4, 6, 5, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![6, 3, 1, 2, 0, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 49 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20130)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 6, 0, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 6, 0, 5], ![3, 1, 2, 6, 0, 4], ![1, 3, 2, 5, 4, 0]], proof := .tail 78 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20131)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 6, 5, 0, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 6, 0, 5], ![3, 1, 6, 2, 0, 4], ![1, 3, 5, 2, 4, 0]], proof := .tail 92 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20132)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 5, 6, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 6, 0, 5], ![3, 1, 2, 6, 0, 4], ![3, 1, 2, 5, 4, 0]], proof := .tail 78 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20133)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 6, 5, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 6, 0, 5], ![3, 1, 6, 2, 0, 4], ![3, 1, 5, 2, 4, 0]], proof := .tail 92 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20134)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![4, 2, 6, 5, 3, 0], ![4, 1, 6, 5, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 6, 0, 5], ![3, 6, 1, 2, 0, 4], ![3, 5, 1, 2, 4, 0]], proof := .tail 70 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20135)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![4, 2, 6, 5, 3, 0], ![4, 1, 6, 5, 0, 3], ![4, 6, 5, 1, 0, 2], ![3, 2, 1, 6, 0, 5], ![6, 3, 1, 2, 0, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 9 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20136)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![4, 6, 2, 5, 3, 0], ![4, 6, 1, 5, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 6, 0, 5], ![3, 6, 1, 2, 0, 4], ![3, 5, 2, 1, 4, 0]], proof := .tail 90 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20137)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![4, 6, 2, 5, 3, 0], ![4, 6, 1, 5, 0, 3], ![4, 6, 5, 1, 0, 2], ![3, 2, 1, 6, 0, 5], ![6, 3, 1, 2, 0, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 49 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20138)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![6, 4, 2, 5, 3, 0], ![4, 6, 1, 5, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 6, 1, 0, 5], ![3, 6, 1, 2, 0, 4], ![3, 5, 2, 4, 1, 0]], proof := .tail 90 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20139)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![6, 4, 2, 5, 3, 0], ![4, 6, 1, 5, 0, 3], ![4, 6, 5, 1, 0, 2], ![3, 2, 6, 1, 0, 5], ![6, 3, 1, 2, 0, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 106 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20140)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![6, 4, 2, 5, 3, 0], ![6, 4, 1, 5, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 6, 2, 1, 0, 5], ![3, 6, 1, 2, 0, 4], ![3, 5, 4, 2, 1, 0]], proof := .tail 11 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20141)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![6, 4, 2, 5, 3, 0], ![6, 4, 1, 5, 0, 3], ![4, 6, 5, 1, 0, 2], ![3, 6, 2, 1, 0, 5], ![6, 3, 1, 2, 0, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 11 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20142)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![6, 4, 2, 5, 3, 0], ![6, 4, 1, 5, 0, 3], ![6, 4, 5, 1, 0, 2], ![6, 3, 2, 1, 0, 5], ![6, 3, 1, 2, 0, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 89 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20143)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![4, 5, 2, 3, 6, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 0, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .low6 (![142, 71, 100, 56, 30, 27, 145, 29, 93, 48, 13, 17, 67, 25, 143, 13, 42, 113, 47, 80, 126, 69, 139, 117, 38, 74, 15, 45]) }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20144)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![4, 5, 2, 3, 6, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 0, 6, 3], ![4, 5, 1, 0, 6, 2], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 44 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20145)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![4, 5, 2, 6, 3, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 0, 6, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 58 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20146)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![4, 5, 2, 6, 3, 1], ![4, 5, 2, 6, 3, 0], ![4, 5, 1, 0, 6, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![3, 1, 0, 2, 4, 5]], proof := .low6 (![10, 14, 97, 72, 136, 27, 2, 102, 91, 26, 85, 124, 123, 131, 147, 37, 82, 68, 88, 116, 1, 130, 96, 63, 118, 122, 141, 54]) }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20147)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![4, 5, 2, 3, 6, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 0, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 75 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20148)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![4, 5, 2, 3, 6, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 0, 6, 3], ![4, 5, 1, 0, 6, 2], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![1, 0, 3, 2, 5, 4]], proof := .tail 44 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20149)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![4, 5, 2, 6, 3, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 0, 6, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![1, 3, 0, 2, 5, 4]], proof := .tail 58 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20150)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![4, 5, 2, 6, 3, 1], ![4, 5, 2, 6, 3, 0], ![4, 5, 1, 0, 6, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![3, 1, 0, 2, 5, 4]], proof := .low6 (![10, 14, 87, 72, 19, 134, 16, 128, 107, 65, 84, 31, 101, 4, 147, 66, 31, 68, 88, 73, 31, 64, 125, 105, 41, 3, 66, 31]) }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20151)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![4, 5, 6, 2, 3, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 6, 0, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![1, 3, 2, 0, 4, 5]], proof := .tail 119 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20152)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![4, 5, 6, 2, 3, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 6, 0, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![1, 3, 2, 0, 5, 4]], proof := .tail 119 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20153)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![4, 6, 5, 2, 3, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 6, 0, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 6, 0, 4], ![1, 3, 2, 5, 0, 4]], proof := .tail 46 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20154)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![4, 5, 6, 2, 3, 1], ![4, 5, 2, 6, 3, 0], ![4, 5, 1, 6, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![3, 1, 2, 0, 4, 5]], proof := .tail 119 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20155)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![4, 5, 6, 2, 3, 1], ![4, 5, 2, 6, 3, 0], ![4, 5, 1, 6, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![3, 1, 2, 0, 5, 4]], proof := .tail 119 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20156)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![4, 6, 5, 2, 3, 1], ![4, 5, 2, 6, 3, 0], ![4, 5, 1, 6, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 6, 0, 4], ![3, 1, 2, 5, 0, 4]], proof := .tail 46 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20157)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![4, 5, 6, 2, 3, 1], ![4, 5, 6, 2, 3, 0], ![4, 5, 6, 1, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![3, 2, 1, 0, 4, 5]], proof := .low0 (![50, 24, 59, 20, 52, 61, 23, 140, 6, 57, 138, 109, 77, 132, 140, 140, 140, 140, 112, 138, 76, 0, 138, 22, 0, 144, 138, 148]) }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20158)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![4, 5, 6, 2, 3, 1], ![4, 5, 6, 2, 3, 0], ![4, 5, 6, 1, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![3, 2, 1, 0, 5, 4]], proof := .low0 (![81, 86, 51, 20, 52, 61, 23, 104, 6, 57, 138, 109, 21, 28, 8, 104, 104, 104, 112, 138, 76, 0, 138, 22, 0, 144, 138, 148]) }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20159)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![4, 6, 5, 2, 3, 1], ![4, 5, 6, 2, 3, 0], ![4, 5, 6, 1, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 6, 0, 4], ![3, 2, 1, 5, 0, 4]], proof := .tail 18 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20160)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![4, 6, 5, 2, 3, 1], ![4, 6, 5, 2, 3, 0], ![4, 5, 6, 1, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 2, 6, 1, 0, 4], ![3, 2, 5, 1, 0, 4]], proof := .tail 149 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20161)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![4, 6, 5, 2, 3, 1], ![4, 6, 5, 2, 3, 0], ![4, 6, 5, 1, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![3, 6, 2, 1, 0, 4], ![3, 5, 2, 1, 0, 4]], proof := .tail 92 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20162)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![4, 6, 5, 2, 3, 1], ![4, 6, 5, 2, 3, 0], ![4, 6, 5, 1, 0, 3], ![4, 6, 5, 1, 0, 2], ![3, 2, 1, 0, 6, 5], ![6, 3, 2, 1, 0, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 135 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20163)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 6, 0, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 6, 0, 5], ![3, 2, 1, 6, 0, 4], ![1, 3, 2, 5, 4, 0]], proof := .tail 129 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20164)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![4, 5, 2, 6, 3, 0], ![4, 5, 1, 6, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 6, 0, 5], ![3, 2, 1, 6, 0, 4], ![3, 1, 2, 5, 4, 0]], proof := .tail 129 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20165)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![4, 5, 6, 2, 3, 0], ![4, 5, 6, 1, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 6, 0, 5], ![3, 2, 1, 6, 0, 4], ![3, 2, 1, 5, 4, 0]], proof := .tail 5 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20166)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![4, 6, 5, 2, 3, 0], ![4, 5, 6, 1, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 6, 0, 5], ![3, 2, 6, 1, 0, 4], ![3, 2, 5, 1, 4, 0]], proof := .tail 33 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20167)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![4, 6, 5, 2, 3, 0], ![4, 6, 5, 1, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 6, 0, 5], ![3, 6, 2, 1, 0, 4], ![3, 5, 2, 1, 4, 0]], proof := .tail 92 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20168)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![4, 6, 5, 2, 3, 0], ![4, 6, 5, 1, 0, 3], ![4, 6, 5, 1, 0, 2], ![3, 2, 1, 6, 0, 5], ![6, 3, 2, 1, 0, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 5 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20169)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![6, 4, 5, 2, 3, 0], ![4, 5, 6, 1, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 6, 1, 0, 5], ![3, 2, 6, 1, 0, 4], ![3, 2, 5, 4, 1, 0]], proof := .tail 39 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20170)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![6, 4, 5, 2, 3, 0], ![4, 6, 5, 1, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 6, 1, 0, 5], ![3, 6, 2, 1, 0, 4], ![3, 5, 2, 4, 1, 0]], proof := .tail 92 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20171)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![6, 4, 5, 2, 3, 0], ![4, 6, 5, 1, 0, 3], ![4, 6, 5, 1, 0, 2], ![3, 2, 6, 1, 0, 5], ![6, 3, 2, 1, 0, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 39 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20172)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![6, 4, 5, 2, 3, 0], ![6, 4, 5, 1, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 6, 2, 1, 0, 5], ![3, 6, 2, 1, 0, 4], ![3, 5, 4, 2, 1, 0]], proof := .tail 114 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20173)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![6, 4, 5, 2, 3, 0], ![6, 4, 5, 1, 0, 3], ![4, 6, 5, 1, 0, 2], ![3, 6, 2, 1, 0, 5], ![6, 3, 2, 1, 0, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 114 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20174)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![6, 4, 5, 2, 3, 0], ![6, 4, 5, 1, 0, 3], ![6, 4, 5, 1, 0, 2], ![6, 3, 2, 1, 0, 5], ![6, 3, 2, 1, 0, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 36 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20175)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![5, 4, 2, 3, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 0, 3, 6], ![4, 1, 5, 0, 2, 6], ![3, 2, 1, 5, 0, 6], ![1, 3, 2, 4, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 62 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20176)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![5, 4, 2, 3, 6, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 0, 6, 3], ![4, 1, 5, 0, 6, 2], ![3, 2, 1, 5, 0, 6], ![1, 3, 2, 4, 0, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 7 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20177)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![5, 4, 2, 6, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 0, 6, 3], ![4, 1, 5, 6, 0, 2], ![3, 2, 1, 5, 0, 6], ![1, 3, 2, 4, 0, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 7 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20178)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![5, 4, 6, 2, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 6, 0, 3], ![4, 1, 5, 6, 0, 2], ![3, 2, 1, 5, 0, 6], ![1, 3, 2, 4, 0, 6], ![1, 3, 2, 0, 4, 5]], proof := .tail 108 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20179)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 6, 0, 3], ![4, 1, 5, 6, 0, 2], ![3, 2, 1, 5, 6, 0], ![1, 3, 2, 4, 0, 6], ![1, 3, 2, 4, 0, 5]], proof := .tail 60 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20180)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 6, 0, 3], ![4, 1, 5, 6, 0, 2], ![3, 2, 1, 5, 6, 0], ![1, 3, 2, 4, 6, 0], ![1, 3, 2, 4, 5, 0]], proof := .tail 95 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20181)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 6, 0, 3], ![4, 1, 5, 6, 0, 2], ![3, 2, 1, 6, 5, 0], ![1, 3, 2, 6, 4, 0], ![1, 3, 2, 5, 4, 0]], proof := .tail 35 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20182)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 5, 0, 3], ![4, 1, 5, 6, 0, 2], ![3, 2, 1, 6, 5, 0], ![1, 3, 6, 2, 4, 0], ![1, 3, 5, 2, 4, 0]], proof := .tail 32 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20183)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 5, 0, 3], ![4, 1, 6, 5, 0, 2], ![3, 2, 1, 6, 5, 0], ![1, 6, 3, 2, 4, 0], ![1, 5, 3, 2, 4, 0]], proof := .tail 7 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20184)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 6, 5, 0, 3], ![4, 1, 6, 5, 0, 2], ![3, 2, 1, 6, 5, 0], ![6, 1, 3, 2, 4, 0], ![5, 1, 3, 2, 4, 0]], proof := .tail 7 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20185)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![4, 2, 6, 3, 5, 0], ![4, 1, 6, 5, 0, 3], ![4, 6, 1, 5, 0, 2], ![3, 2, 1, 6, 5, 0], ![6, 1, 3, 2, 4, 0], ![5, 3, 1, 2, 4, 0]], proof := .tail 40 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20186)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![4, 6, 2, 3, 5, 0], ![4, 6, 1, 5, 0, 3], ![4, 6, 1, 5, 0, 2], ![3, 2, 1, 6, 5, 0], ![6, 1, 3, 2, 4, 0], ![5, 3, 2, 1, 4, 0]], proof := .tail 111 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20187)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 4, 2, 3, 5, 0], ![4, 6, 1, 5, 0, 3], ![4, 6, 1, 5, 0, 2], ![3, 2, 6, 1, 5, 0], ![6, 1, 3, 2, 4, 0], ![5, 3, 2, 4, 1, 0]], proof := .tail 127 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20188)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 4, 2, 3, 5, 0], ![6, 4, 1, 5, 0, 3], ![4, 6, 1, 5, 0, 2], ![3, 6, 2, 1, 5, 0], ![6, 1, 3, 2, 4, 0], ![5, 3, 4, 2, 1, 0]], proof := .tail 137 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20189)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 4, 2, 3, 5, 0], ![6, 4, 1, 5, 0, 3], ![6, 4, 1, 5, 0, 2], ![6, 3, 2, 1, 5, 0], ![6, 1, 3, 2, 4, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 120 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20190)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![5, 4, 2, 3, 6, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 0, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 2, 1, 5, 0, 6], ![3, 1, 2, 4, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 62 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20191)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![5, 4, 2, 3, 6, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 0, 6, 3], ![4, 5, 1, 0, 6, 2], ![3, 2, 1, 5, 0, 6], ![3, 1, 2, 4, 0, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 7 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20192)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![5, 4, 2, 6, 3, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 0, 6, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 5, 0, 6], ![3, 1, 2, 4, 0, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 7 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20193)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![5, 4, 2, 6, 3, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 5, 0, 6, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 5, 0, 6], ![3, 1, 2, 4, 0, 6], ![3, 1, 0, 2, 4, 5]], proof := .tail 7 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20194)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![5, 4, 6, 2, 3, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 6, 0, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 5, 0, 6], ![3, 1, 2, 4, 0, 6], ![1, 3, 2, 0, 4, 5]], proof := .tail 108 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20195)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![5, 4, 6, 2, 3, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 5, 6, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 5, 0, 6], ![3, 1, 2, 4, 0, 6], ![3, 1, 2, 0, 4, 5]], proof := .tail 108 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20196)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 6, 0, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 5, 6, 0], ![3, 1, 2, 4, 0, 6], ![1, 3, 2, 4, 0, 5]], proof := .tail 60 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20197)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 5, 6, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 5, 6, 0], ![3, 1, 2, 4, 0, 6], ![3, 1, 2, 4, 0, 5]], proof := .tail 60 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20198)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 6, 0, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 5, 6, 0], ![3, 1, 2, 4, 6, 0], ![1, 3, 2, 4, 5, 0]], proof := .tail 95 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20199)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 6, 0, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 6, 5, 0], ![3, 1, 2, 6, 4, 0], ![1, 3, 2, 5, 4, 0]], proof := .tail 35 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20200)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 6, 5, 0, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 6, 5, 0], ![3, 1, 6, 2, 4, 0], ![1, 3, 5, 2, 4, 0]], proof := .tail 12 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20201)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 5, 6, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 5, 6, 0], ![3, 1, 2, 4, 6, 0], ![3, 1, 2, 4, 5, 0]], proof := .tail 95 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20202)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 5, 6, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 6, 5, 0], ![3, 1, 2, 6, 4, 0], ![3, 1, 2, 5, 4, 0]], proof := .tail 35 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20203)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 6, 5, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 6, 5, 0], ![3, 1, 6, 2, 4, 0], ![3, 1, 5, 2, 4, 0]], proof := .tail 12 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20204)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![4, 2, 6, 5, 3, 0], ![4, 1, 6, 5, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 6, 5, 0], ![3, 6, 1, 2, 4, 0], ![3, 5, 1, 2, 4, 0]], proof := .tail 83 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20205)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![4, 2, 6, 5, 3, 0], ![4, 1, 6, 5, 0, 3], ![4, 6, 5, 1, 0, 2], ![3, 2, 1, 6, 5, 0], ![6, 3, 1, 2, 4, 0], ![5, 3, 1, 2, 4, 0]], proof := .tail 7 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20206)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![4, 6, 2, 5, 3, 0], ![4, 6, 1, 5, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 6, 5, 0], ![3, 6, 1, 2, 4, 0], ![3, 5, 2, 1, 4, 0]], proof := .tail 146 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20207)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 4, 2, 5, 3, 0], ![4, 6, 1, 5, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 6, 1, 5, 0], ![3, 6, 1, 2, 4, 0], ![3, 5, 2, 4, 1, 0]], proof := .tail 127 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20208)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 4, 2, 5, 3, 0], ![6, 4, 1, 5, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 6, 2, 1, 5, 0], ![3, 6, 1, 2, 4, 0], ![3, 5, 4, 2, 1, 0]], proof := .tail 137 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20209)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![4, 6, 2, 5, 3, 0], ![4, 6, 1, 5, 0, 3], ![4, 6, 5, 1, 0, 2], ![3, 2, 1, 6, 5, 0], ![6, 3, 1, 2, 4, 0], ![5, 3, 2, 1, 4, 0]], proof := .tail 111 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20210)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 4, 2, 5, 3, 0], ![4, 6, 1, 5, 0, 3], ![4, 6, 5, 1, 0, 2], ![3, 2, 6, 1, 5, 0], ![6, 3, 1, 2, 4, 0], ![5, 3, 2, 4, 1, 0]], proof := .tail 127 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20211)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 4, 2, 5, 3, 0], ![6, 4, 1, 5, 0, 3], ![4, 6, 5, 1, 0, 2], ![3, 6, 2, 1, 5, 0], ![6, 3, 1, 2, 4, 0], ![5, 3, 4, 2, 1, 0]], proof := .tail 137 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20212)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 4, 2, 5, 3, 0], ![6, 4, 1, 5, 0, 3], ![6, 4, 5, 1, 0, 2], ![6, 3, 2, 1, 5, 0], ![6, 3, 1, 2, 4, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 120 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20213)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![5, 4, 2, 3, 6, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 0, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 2, 1, 5, 0, 6], ![3, 2, 1, 4, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 53 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20214)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![5, 4, 2, 3, 6, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 0, 6, 3], ![4, 5, 1, 0, 6, 2], ![3, 2, 1, 5, 0, 6], ![3, 2, 1, 4, 0, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 110 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20215)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![5, 4, 2, 6, 3, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 0, 6, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 5, 0, 6], ![3, 2, 1, 4, 0, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 110 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20216)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![5, 4, 2, 6, 3, 1], ![4, 5, 2, 6, 3, 0], ![4, 5, 1, 0, 6, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 5, 0, 6], ![3, 2, 1, 4, 0, 6], ![3, 1, 0, 2, 4, 5]], proof := .tail 110 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20217)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![5, 4, 6, 2, 3, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 6, 0, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 5, 0, 6], ![3, 2, 1, 4, 0, 6], ![1, 3, 2, 0, 4, 5]], proof := .tail 119 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20218)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![5, 4, 6, 2, 3, 1], ![4, 5, 2, 6, 3, 0], ![4, 5, 1, 6, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 5, 0, 6], ![3, 2, 1, 4, 0, 6], ![3, 1, 2, 0, 4, 5]], proof := .tail 119 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20219)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![5, 4, 6, 2, 3, 1], ![4, 5, 6, 2, 3, 0], ![4, 5, 6, 1, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 5, 0, 6], ![3, 2, 1, 4, 0, 6], ![3, 2, 1, 0, 4, 5]], proof := .tail 43 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20220)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 6, 0, 3], ![4, 5, 1, 6, 0, 2], ![3, 2, 1, 5, 6, 0], ![3, 2, 1, 4, 0, 6], ![1, 3, 2, 4, 0, 5]], proof := .tail 94 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20221)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![4, 5, 2, 6, 3, 0], ![4, 5, 1, 6, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 5, 6, 0], ![3, 2, 1, 4, 0, 6], ![3, 1, 2, 4, 0, 5]], proof := .tail 94 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20222)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![4, 5, 6, 2, 3, 0], ![4, 5, 6, 1, 0, 3], ![4, 5, 6, 1, 0, 2], ![3, 2, 1, 5, 6, 0], ![3, 2, 1, 4, 0, 6], ![3, 2, 1, 4, 0, 5]], proof := .tail 103 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20223)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (20096 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 20096 ≤ id.val) (hhigh : id.val < 20224) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 20096)) = true := by
  let j : Fin 128 := ⟨id.val - 20096, by omega⟩
  have hsum : 20096 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (20096 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard157
