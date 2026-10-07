import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard036
open N4R2RowDataReplay

-- Original cycle 0011c4f6bac14c4f49bdafa75afde2cc004f18acec267168dbeae2302d888bc7; original global index 8.
def localCycle00000 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 2 2, .triangle 28 1, .gapUpper 4 1, .gapLower 0 4]

-- Original cycle 0054d8def7c3b792cb2847fc3432d3717446815c2170aaab00986e2895fe11ea; original global index 33.
def localCycle00001 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 3, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 01e4f873363a47911bc3208541ec91115ac924f0c4e2354da5f63bd9ae5b7396; original global index 152.
def localCycle00002 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 6 0, .gapLower 0 3, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 035a16a2dfedfaff48a980c9b71b00fa9897eec4047a25138f5aec3c14826ad3; original global index 272.
def localCycle00003 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 3, .gapUpper 3 4, .gapLower 6 4, .triangle 18 0]

-- Original cycle 037ab32ce0e1964d4bfd3e1a11d03438bc64e22d0de829190f85f2c0d036c841; original global index 281.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 8 0, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 0392e1e4bca978ce5f53586037e6fc5fe7f4a030b2dfa004011085a6cfdf3ea7; original global index 287.
def localCycle00005 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 20 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 0438975f9081f4038ae281b6e52a9f91501decb12ad9757fe932d519bf99e328; original global index 332.
def localCycle00006 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .triangle 18 0, .triangle 15 2, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 043e5cdc28b2edbccfe057f1566f4698f417f883b670a53a790fe550731a9f7a; original global index 335.
def localCycle00007 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![4, 0, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 6 0, .triangle 8 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 044e2f9b4a6a79ac2d4c269d70724c87ff329beca0c6a70e9b95d89ae8b0d77a; original global index 339.
def localCycle00008 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 27 0, .gapLower 3 0]

-- Original cycle 06effdc7899f3c03831c63ef21e11417e45020f464c170d82ff9b96bb6c80702; original global index 569.
def localCycle00009 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![4, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 6 0, .triangle 8 0, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 092e7a3461a55e47cfe3ba518977943b58a6c3846e7d95095ba95138d0d6514e; original global index 735.
def localCycle00010 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 09f820e37835339b4d3afa6bd391814bfda47d66bf97aac41ed6cae820b1a5e5; original global index 801.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 0 2, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 0affd810a23d5e40097397e8cf97088afde47cf0fe31bfd0339a05fa43da95c8; original global index 879.
def localCycle00012 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 1 6, .distance 1 5]
    constant := ![2, -2, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 24 1]

-- Original cycle 0b651c88d90f1177b5fefb8c27042042b20ac1fa831ea1dc7baa6efb7bdd4764; original global index 914.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 3, .triangle 8 1, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 0b6a2dbd1e6817fb92680a4282ea5fd17d5ed1080b1acc58de6151519c705b09; original global index 916.
def localCycle00014 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .theta 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, 3, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 29 1, .gapLower 6 0, .corridorUpper 5 6, .gapLower 6 5, .triangle 21 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 0c56fbf0ccc064b3e0132eefbc63a9099a92f67fbe39f1abed3180a486b0d929; original global index 976.
def localCycle00015 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 16 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 0d2ae12ec9101b98d2b8cf1bea31fa2cbe40208a8646140d7e2c0913d178193e; original global index 1046.
def localCycle00016 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 0ddc62d2baa56c983f9a6ffca24fefb3a14dc8bbe40bfccd690821dd450d31e4; original global index 1093.
def localCycle00017 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 0e0dcf95a94e86b464f51fadd03fb3b76364e7e9c5a5eba6a1f40b2969a49660; original global index 1104.
def localCycle00018 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Original cycle 0e4fdfe782d2ca6d71e344cc994c55bd1950fc8a836c348066efb8793152384b; original global index 1126.
def localCycle00019 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 4, .gapLower 6 3, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 0efd237b490fd8e3728053608fd208130b29bebc933d6cfec3e09d136781fe64; original global index 1185.
def localCycle00020 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 6 1, .triangle 5 2, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 1001457d1f722f10daa7f1f96cc5d4cff3ceae0c3c299902d6034517ec6c4293; original global index 1280.
def localCycle00021 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 3]
    constant := ![4, 0, -2, -2, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 11 1, .triangle 10 0, .triangle 26 0, .gapLower 3 0]

-- Original cycle 109c1e6ce7ae26dde994be9501a47b4b51184194e072b6c278f35673b9328462; original global index 1333.
def localCycle00022 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 5 2, .triangle 11 0, .gapLower 6 2, .gapUpper 2 3]

-- Original cycle 11c5d7d7e0cda6cd6aba33bb226008d9db63ebd6d3978ee694a45557f014ad8d; original global index 1414.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 12f252847fdbcde56d3953677430447c5724755577df24e38483d0a5c35a5c13; original global index 1492.
def localCycle00024 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 15a4a592278fc87b0a8541930cc376615eb3e88333a5437dc8fa483f16ec7902; original global index 1717.
def localCycle00025 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 2, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 185126b2611ef9ccfdb1b32b87e3440ee9c5657cc473da0ef3006a86f2292ace; original global index 1906.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 6 0, .triangle 8 2, .gapLower 6 3, .triangle 27 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 19b1f8a16adf507348ec91368930473913f9ccf730679da2f5b4e99eda77b63a; original global index 2007.
def localCycle00027 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 1af9e07cbd758269f21cb13ac6dfb727852a176122a44a0795bdb281c044f287; original global index 2090.
def localCycle00028 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .triangle 11 1, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 1ed9b5089426b83901c48d4fbc29913e2d8a210e0263d80f1b213d0ef168a3bc; original global index 2369.
def localCycle00029 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 1f9cc41ff9a6c18938f1811e3e6356fbef04f0cdd9044afcceccf258c93482ad; original global index 2433.
def localCycle00030 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, 0, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 20 1, .triangle 1 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 2015960863b1b219247b6f3cd743cd2bf322cc9365f4c68f86e2c9bdf7cede88; original global index 2463.
def localCycle00031 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 29 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 20c259074fc1a51b24f8d045aea92febbdb1e69bf5411d65ee9d474881b4b2a1; original global index 2511.
def localCycle00032 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 227f6a493c616b231f78ecc2b6fac89880ba8c4142ef628dace8663a3a4715c1; original global index 2640.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 22a086fe123e66fa2c525577c753037613f117890dafa55cc8f739fd337d658b; original global index 2650.
def localCycle00034 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 6 0, .triangle 7 2, .gapLower 0 2, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 22ec3129feb537e6d9eea9623d54d60784a69b57e3bc2b755f86ce28f7edeb80; original global index 2680.
def localCycle00035 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, -1, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 0, .gapLower 6 4, .triangle 4 2, .triangle 8 1, .triangle 29 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 25671f91f6e70f85da07223085d49baf010cfa71886305f866e8b1b2cb802cbd; original global index 2877.
def localCycle00036 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 2616284275bbe78ac7228c374925eb4b7049064fe20bcacde908d14d90b9f62e; original global index 2918.
def localCycle00037 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 17 1, .triangle 16 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 262e8760a3595cb0a10d62795b2a47650dccaec77d64dc9a76f5b004f09d5152; original global index 2927.
def localCycle00038 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 26b3d20b3c1f0a4c5bfbeec7b7f4a2f925951e21ef61ccd9a0b82b3329d92a1e; original global index 2967.
def localCycle00039 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 8 0, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 28d1de460877074b01395b7d992a2bdcf03147f847106d68029402a801de6af4; original global index 3126.
def localCycle00040 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 29 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 29b419966c09a13c5a7043e7cdd5589ca3fcfa7bb4a946d309c77829fbd53ae4; original global index 3182.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 2a5e02c26e3e4bb66b97efd944f6c7cec38383ba6953d3ba462e2af7a0f9e841; original global index 3230.
def localCycle00042 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 13 2, .gapLower 6 1, .gapUpper 4 2]

-- Original cycle 2a95d206e9f9172b3622fc10ad7fa1d0a8afbd8bd5987248feb914ca347b8110; original global index 3240.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 2dad78b0ee81cf0d8d0049a33c17146f94b8128fe26132e7e21c7b4f69554bee; original global index 3486.
def localCycle00044 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 21 2, .gapLower 6 3, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 2e5cf0192ba2dbcfdfaca20c9a868adeecc48c20edb1f7159ed9cca068c2499f; original global index 3545.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 6 2, .triangle 8 1, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 2e711ba68ff10dc4f929cfcd8e0c241952a9297f89e3c2f36e083580c44ccc67; original global index 3551.
def localCycle00046 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 1 3]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 21 0]

-- Original cycle 2f65ffdff4303c756cb3eabe3c087dd4ab87b219d95dda2c89f4be3307f34266; original global index 3624.
def localCycle00047 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 0 2, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 2f95a6fcea7b5bddb2e2966734c71d2eb95c76f5a1924dc847718a86367ebe30; original global index 3636.
def localCycle00048 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 20 1, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 308c3ad95e1baac6512977f87a5c61ab17ef15c3fd51ffd30fb434ff1b14556e; original global index 3700.
def localCycle00049 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, 3, 0, -2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 29 1, .gapLower 6 0, .corridorUpper 5 6, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .triangle 11 1, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 30e7d430e2ca1b5058f3a171d2934a5fd8a79be964c0edee2480bfa2192a1c03; original global index 3730.
def localCycle00050 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 3206c2aca7efe9a1ac232827444299399b41559882323d83d35311d81328e327; original global index 3818.
def localCycle00051 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, 0, -1, 0, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 13 1, .triangle 6 1, .triangle 7 0, .triangle 28 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 331de03e5e7ec5e1bde8df188b899eed5f91c05707135858759f70d482025630; original global index 3912.
def localCycle00052 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![4, 0, -1, 0, -1, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 16 0, .triangle 15 2, .triangle 21 0, .gapLower 6 3, .triangle 8 1, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 368df2626ca45afa1a79b8eae932b2ba95e23423dce56dea6e2b868298b9f46d; original global index 4190.
def localCycle00053 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 21 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 36f24ce6597a830a020b487eb6687d389f38a024066309a71b9aad3ade76463a; original global index 4219.
def localCycle00054 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 1 3]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 21 0]

-- Original cycle 3840c2fbef6624534cb0424229edea200238b69dc9303b04624e26cfb6906a29; original global index 4318.
def localCycle00055 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 384d50ea4636d17235f2313564d33fa53427b4bbed64559f6c5c4f3ffcd5ff2e; original global index 4323.
def localCycle00056 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 3 6, .distance 2 6, .distance 0 2]
    constant := ![0, -3, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.triangle 8 2, .gapLower 6 3, .triangle 27 2, .gapUpper 2 3]

-- Original cycle 385d5e2804c747daea1bd65cb218e46c0193f4da5af40d6269c5c832eb8e4ead; original global index 4330.
def localCycle00057 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 399183be39d113a17b3a05eab3a841a17c5bc4cdda4ed3b2cce0d9718629ce99; original global index 4436.
def localCycle00058 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -1, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 13 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 39c437d7bd799becbb60f8ed0774c72318262f6578dfe44dc75aff2fd12c8703; original global index 4459.
def localCycle00059 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 8 0, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 3d4b1120274a2630565f6b9e7861c2333a5d8be69400e96b476f947924925b67; original global index 4748.
def localCycle00060 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 6 1, .gapLower 6 0]

-- Original cycle 3db72acc68d91a1f6dadb4f604a400c15dfb7c87c2550efe4fe87126b597b3d6; original global index 4778.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 29 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 3ef8efd37cd52ce071520a2a4895b121a43a9608fa3784e16af92b30356d5d58; original global index 4868.
def localCycle00062 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![4, 0, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 4, .triangle 11 1, .triangle 27 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 413f78b88681f09cfb3e08b647bea44486e656fe6a04bd4b0e6438a3e9a403d8; original global index 5036.
def localCycle00063 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 4, .distance 0 3]
    constant := ![-1, -3, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 11 0, .gapLower 6 2, .triangle 29 1, .gapUpper 4 2, .triangle 9 1]

-- Original cycle 429c7da6472282c85aac71dfbea0059b79494cacb642c83c0051b09b4ab32d02; original global index 5131.
def localCycle00064 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 21 1, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 436385209c8bff194238a5f8b44b978fbb7a80c3f2943b5e4df4f94574b84b58; original global index 5202.
def localCycle00065 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 4, .triangle 11 1, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 43a37183df685441279f8c4436f4b758d784751c3d3f8ec1bfbfd9781abad5fe; original global index 5231.
def localCycle00066 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .gapLower 6 2, .triangle 8 1, .triangle 5 2, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 43c7e7e8dff3260737ec5f000eab6ae829f183b83df35d2d7e790eb38391212d; original global index 5244.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 29 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 4517d11f01a003af6d8e1203b191362560941f778b86e5dc65bb0faebf99c6ff; original global index 5344.
def localCycle00068 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 3, .triangle 4 2, .triangle 11 1, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 456b9f214753d388d665e808f62bf3433a7b507c31e83c1892b8a197b52e952d; original global index 5368.
def localCycle00069 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 0 2, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 6 1, .gapLower 0 3, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 45bc6dd9a17d3987b739c04cd4a1a9d78dd17c1a7e6d4cb5685c4c7ac68058bd; original global index 5392.
def localCycle00070 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 4, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 460fd9d1d731eab3a74dd77dfe4211a1637aa8ba6ab8609bba8f001bcfa02b8f; original global index 5421.
def localCycle00071 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 4870d62b00db3188f96eddd7e020813185fe44257a9344e2690c6db5e9147157; original global index 5611.
def localCycle00072 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 492b0c150869277a440de2d3e94ae5a66862b8f77240c2edcb861dd166c81149; original global index 5666.
def localCycle00073 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Original cycle 4949ac11fc9c70a71713b2fcda8c8452fe03fd6d747f2d8f398298638180ac2f; original global index 5675.
def localCycle00074 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 1 5]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 24 1]

-- Original cycle 4a7c8690e91e065152c7643967d89757c29f11c3bc644f15d15b0131d8cfc079; original global index 5774.
def localCycle00075 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 8 0, .gapLower 2 2, .gapLower 5 1, .corridorLower 4 5]

-- Original cycle 4cf0c6b28d77e248570e2372f100bd8098d8fb4d3d8154cc9d23c89137d48aa9; original global index 5975.
def localCycle00076 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 4e214d7ad526e2afb74c23d5b719b3f58d3c73bb8407e9fa822d7d71b5b59294; original global index 6063.
def localCycle00077 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![4, 0, -1, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 31 2, .triangle 33 0, .gapLower 6 4, .triangle 4 2, .triangle 8 1, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 4e9451ba2af53c94b76ff4d0e792779f0bab314233cc39004ec4a7f49cc46c74; original global index 6105.
def localCycle00078 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 8 2, .gapLower 6 2, .gapUpper 2 3]

-- Original cycle 4eed0834ef489cf7bda70c43372c3e2e7c0e7679366930ed4722cf85a11d025f; original global index 6132.
def localCycle00079 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 3, .gapUpper 3 4, .gapLower 6 4, .triangle 18 0]

-- Original cycle 519a0f687a56230423bbc07655dcfb4983740d48f4ef801b8d525f4265426f1b; original global index 6349.
def localCycle00080 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 21 1, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 52ab866aacf7887e45da17144cde3b1fd5cc895ebb61c59e33dbfd44a174f98c; original global index 6425.
def localCycle00081 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 52b3ae734d65428bc66c01dbce183cf3b25928ff61fe8bc42d28a1f0021bd41d; original global index 6431.
def localCycle00082 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 15 2, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 5326c09d72a0977ed7d133d2c9778d8e21de4ba77d7301dcea286f2df1025f69; original global index 6470.
def localCycle00083 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![4, -1, 0, -3, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 2 6, .triangle 16 0, .triangle 18 2, .gapLower 6 4, .triangle 11 1, .triangle 27 0, .corridorLower 2 3]

-- Original cycle 550925787b788d1fc18ac2d39331802a1453e4498ea45c007d7a92a0813ebc93; original global index 6585.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 0 2, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 5999f6bb3724ccbac5f49682840d2d7f6e76daea1d9d01e798e45f48658afc17; original global index 6965.
def localCycle00085 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .triangle 4 2, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 5bcdf6f2a4e725e4f8d1512e504304bf0e3c851f95e37bb016e2134f7d9fde61; original global index 7135.
def localCycle00086 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 5]
    constant := ![2, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 24 1]

-- Original cycle 5d5b39a0baba93d7cace49dca5240a4d8c6e89bafdbd6f2f2ff07760fe31045b; original global index 7267.
def localCycle00087 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 8 0, .triangle 5 2, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 5d8d39d95b903be3af607c39879fbb004cd99f5a86ac20e60c3b17d8c52d10ab; original global index 7282.
def localCycle00088 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 3, .triangle 8 1, .triangle 29 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 5fb910de87a0ac7dd8db5eb62c0b06982264176b05ab56e1d60916a5bdb08c49; original global index 7458.
def localCycle00089 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -3, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 6 2, .triangle 8 1, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 5fe1dabdd9f8b04f57eddc95c5536879813b30ed23c7906243c3ce0c189d7d5c; original global index 7474.
def localCycle00090 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 60778c7929f37139bbc9b97d9bf26a79eee57c7d3a12aacf334bc16a7af221f9; original global index 7512.
def localCycle00091 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 24 1, .triangle 20 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 610d30e06e331ffa4749c7e6c6c5090781c006cd790506cbce6b7581c9c26ce8; original global index 7569.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 3, .triangle 8 1, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 61110d9b2954e3fe47401bd0922129db6fb222eee9be4c9e1c179ddcd2183f0f; original global index 7571.
def localCycle00093 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 2, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 6369a3d6e0f83397e18379cab37df680c33597a04fa7447f564a1ba76d676487; original global index 7757.
def localCycle00094 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 29 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 65d5da5e8535d5e31243017dac69404f9dd5981dfb0bb6ae265c47ba6d34cec3; original global index 7926.
def localCycle00095 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 663aafed64651fca64785967c051226bb4c1ae82f703293ec4e3c67963802ac4; original global index 7952.
def localCycle00096 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, -2, 0, 3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, -1, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapUpper 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 67d3e89ef155d273bfc3f662f29c01d33db6ada4f92f361c3b053d5956629635; original global index 8070.
def localCycle00097 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 4, .triangle 11 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 68da57c408af60bd68df9b8e96ae83ec5eea5db37abc730277bcbfe8bb4592dd; original global index 8159.
def localCycle00098 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 6b367561438eaeb04d6388f567dd0f21d34c204877918d15cacf7bcdd5b6518a; original global index 8345.
def localCycle00099 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -3, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 8 0, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 6bb2f54c75747e47550618d680e1ad8369db561d14296b2291fe4ed39522756f; original global index 8381.
def localCycle00100 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 6c52e8b35653e2608f7c5a7067ea69774d1f2198d445956673f994666b89604c; original global index 8439.
def localCycle00101 : Cycle where
  length := 5
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle 6cf291bf46e0e3e3e9fa7dafddee75c5f5e34f1d7a69da50484c3bb0d278a353; original global index 8477.
def localCycle00102 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 6deb4ca7bef31208d819a95433433084a8e2ef321c6132e0b3862ea97b52012c; original global index 8537.
def localCycle00103 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .gapLower 6 3, .triangle 21 1]

-- Original cycle 6e700030893f7c6db3d7397b3be4bec96185911c0143a992c9b83f3b7748b201; original global index 8570.
def localCycle00104 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 1 6, .distance 1 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .triangle 21 1]

-- Original cycle 6ec054ad8fc45a3292fcb9b9e18860f81145995c5308a732cdc524fc492228d5; original global index 8594.
def localCycle00105 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 6ecf11c3f5c7cc8daa6217b6e055c34f2e65f79ea0a72956c0450b517517cb8f; original global index 8598.
def localCycle00106 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 73de9351547da3a4cb72adbecc272e5b66c5fb10511b7697b5152dbab41e74db; original global index 8985.
def localCycle00107 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 4, .distance 0 3]
    constant := ![-1, -2, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 11 0, .gapLower 6 2, .triangle 29 1, .gapUpper 4 2, .triangle 9 1]

-- Original cycle 7501a9183cfc87aaf81feb6a9ad72c8b885181e45e558909cbe00fbe9fe55896; original global index 9067.
def localCycle00108 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 7660a91bcc9db1900631003d3bc5d9a5aa5922bc61767fafebe430a534e868fe; original global index 9163.
def localCycle00109 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 3 6, .distance 1 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 21 2, .gapLower 6 4, .gapUpper 3 4]

-- Original cycle 79558bf2a55353d1771fdbd8c9509b2d3688435e780b3ec56ea47668c83a3836; original global index 9390.
def localCycle00110 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 11 1, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 7ac4fc4217f305d13b6eb58bcd6295a60919abf2f98191ffaf1ea17568ce6004; original global index 9503.
def localCycle00111 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 10 1, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 7b0ba59653c6ff7536ebec0ca9d38a8ec906ee4e6d0ba3a1621e0660fb107a17; original global index 9529.
def localCycle00112 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 7c561e78c172cc04a233213090262effe4f7258bed80e27dc5e458581908337d; original global index 9625.
def localCycle00113 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 7d78f391f79b6ad01442b844b3f2feb782d02b25da15dfd8a0b003f611d3e993; original global index 9732.
def localCycle00114 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 6, .distance 1 3]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .triangle 21 1]

-- Original cycle 7dc640cc2349964a71324ff65593ae385c02a4f4c51c03090efeccc62b07a233; original global index 9765.
def localCycle00115 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 7 2, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 7e882373c3506641ea66a739fabe5ae94f014d42e1eb434a45a6d5e4bd2072ab; original global index 9824.
def localCycle00116 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .triangle 17 1, .triangle 16 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 803a12a903f0c8e4f4d7514bd1b2f3419e2c154a3b7703f1198dc2312413d113; original global index 9947.
def localCycle00117 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 80f4abd68f8a86f32efc3a1bea68324a9e2d2fc71b55a95f9322655768fba796; original global index 10007.
def localCycle00118 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 2, .triangle 21 0, .gapLower 6 3, .triangle 8 1, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 828a1cac9ed8bb76e94000cf168fa918a9da91ec5b9d068c0832343eeacb3a09; original global index 10131.
def localCycle00119 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 0 2]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 5 2, .gapUpper 2 2]

-- Original cycle 8413651eb0f9e7d91d402b57de8a0893e2290de0a04ee5297ae4dcb0e5e7ac36; original global index 10254.
def localCycle00120 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .triangle 4 2, .gapLower 6 2, .triangle 29 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 846c9cf5033963ca6cf0adde8a4101c0a85813411dd19ec4db9fd9e2ccfcc9ee; original global index 10284.
def localCycle00121 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .gapLower 6 2, .corridorLower 2 6, .thetaLower 2]

-- Original cycle 8507afc2710ccd4056452517605c97a43ad444497c9329379cad24e08b64a7b6; original global index 10325.
def localCycle00122 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .gapLower 6 1, .corridorLower 4 6, .thetaLower 4]

-- Original cycle 85beadd09ce5d1e845a18842d00d133151387994901b4056bbe07a5ea7d1a11b; original global index 10380.
def localCycle00123 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 8604cf705b5f34a506fe383518c4414a160d1fe5427b48382bfd59266d48a708; original global index 10396.
def localCycle00124 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 86217cdfa261c016200448a7f2c3653bb10108db52a3dc0d3ec8b51524464e6a; original global index 10404.
def localCycle00125 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -3, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 3, .triangle 11 1, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 872cb0e5d90e579147ddbdb14be481768747d6c59365b90ee05c7e8aa4b4c3db; original global index 10488.
def localCycle00126 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .triangle 18 0, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 899d3c12c260e452f09b46dc1c3d5e5ea8b0f775e67039a63e87e81784ced8ee; original global index 10660.
def localCycle00127 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 8aca7b79baf831805083d82b0de4bc09410a5bd86824196127da7c201d01d88e; original global index 10754.
def localCycle00128 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![4, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 19 0, .triangle 21 0, .triangle 27 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 8ea98c4022292319837990411b292e4a08022a841e42336f539e6dfdf7186544; original global index 11039.
def localCycle00129 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .gapLower 6 2, .triangle 8 1, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 8ff35206b76948545dfd3423fd840bd9d0357a2580a0174eea9ae748d6c3ed3b; original global index 11144.
def localCycle00130 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 90b8f82100c56db633072360ea6832a8d3076f02333f079e19ce2b0c96b5d425; original global index 11206.
def localCycle00131 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![4, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 11 0, .triangle 27 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 92df37f0bea3ce68eeea81ff35552ea385274a0a999225a2f24c87d738a8bfd4; original global index 11386.
def localCycle00132 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 0 2, .distance 2 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 0 2, .triangle 8 0, .triangle 27 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 935eaeb414d65cfd77a988f439947ba6367e6a4768a9e25b7e26726211712e47; original global index 11429.
def localCycle00133 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 1 6, .distance 1 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 24 1]

-- Original cycle 93929d2cacea09cc4cc240f8146baeab38748e480f8d3bad42888dd9656ff5e6; original global index 11448.
def localCycle00134 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .gapLower 6 3, .triangle 8 1, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 94914f42ebd57d59e906d579fa50c073d7da733de2202f3e5fc2ccabb77818be; original global index 11527.
def localCycle00135 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .gapLower 1 4, .gapLower 2 3, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 94c848c021bd469ade212c271ae1ae5ecdd58f1d68668bae154d66e23fbd5f5d; original global index 11547.
def localCycle00136 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 955258db42e19a3025c6adf42104c5464a7579b89194352f21b348ba42a101d8; original global index 11602.
def localCycle00137 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 20 1, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 963e4a47971ed72f8c934f1310a3c0f056ee1544fc7ead43330abb150a376af8; original global index 11682.
def localCycle00138 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -2, -2, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 6 0, .gapLower 0 3, .gapLower 0 2, .triangle 1 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 970a0cf8599c8415d6fb009de551d25ffaebf83ba48ad17472a816524f559710; original global index 11738.
def localCycle00139 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 3, .triangle 21 1, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 973d196ce4cae0a238a7de1adb2afc18b1ef9ccd73e3397cca54f5f7e5038c5b; original global index 11752.
def localCycle00140 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 4 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle 97996238a5dcff1f1a654f573608ab2291fe10122ecbddd7ddccc62cb02f4d67; original global index 11775.
def localCycle00141 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 9910d74086237445f4c7821994dfef123af261fb25a5176211cbdcb488fcd2e9; original global index 11885.
def localCycle00142 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 996ebaea7bab9a91cc73c8a814387eaf915e03a49ed7375610bbecebdd1d74b7; original global index 11916.
def localCycle00143 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 9a9326a6eba7e20061165cf6f2076a0fe0555ddba9a0f2d6b5033e2c76aed828; original global index 12008.
def localCycle00144 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 6 0, .gapLower 0 3, .triangle 3 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 9cdf3390db7765d4a6483367f2fffa98fbe62d9c73ea2e958dc1657c049116f9; original global index 12203.
def localCycle00145 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 6 0, .triangle 7 2, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 9df42fd75c29f8d119641d68704db1a9a23c11aec43eca146d46053d892a5d10; original global index 12294.
def localCycle00146 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 5]
    constant := ![2, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 18 2, .triangle 24 1]

-- Original cycle 9e63b68b91649d67792b16e304f31d2166cf55a47b793432a826cfab76b0d47f; original global index 12333.
def localCycle00147 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 29 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle a04d479139b243b9dfa2cd40300d949d8d81e716eeb8afbcd5e3ceec090bbf5f; original global index 12473.
def localCycle00148 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle a05633a0aa68ed97fc1b9221a80f582694eff11c8a2b645b3fd6240b0916626d; original global index 12478.
def localCycle00149 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 3 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 4, .gapLower 6 3, .triangle 8 1, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle a15f2ff475bee1a96207ee40c2c60a9ed9c9ba86ece32ce4f71c3834ffc42bf9; original global index 12548.
def localCycle00150 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 20 1, .triangle 1 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle a185903b862c66e77dd80a31aef46dcba2f3d3b43d3f3889d240986c8796dc73; original global index 12561.
def localCycle00151 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .theta 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, 2, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 29 1, .gapLower 6 0, .gapLower 6 6, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle a456679ff01b28407d699c3c45d45e5de753f0090ff0e39d408f4c62b3620ee6; original global index 12776.
def localCycle00152 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, 3, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 29 1, .gapLower 6 0, .corridorUpper 5 6, .triangle 33 2, .gapLower 6 4, .triangle 21 1, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle a4e11ca23b151a210915128123c4b4e2777fc0ba616b76cb4592ad80bff1c3e0; original global index 12814.
def localCycle00153 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 26 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle a6ef9d476ed8df4df17d349c5fafd0e223bcd78e6e409eed83662c879011d9ed; original global index 12969.
def localCycle00154 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 2 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 2, .gapLower 6 2, .triangle 29 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle a7477e451c9707f5f6348e29207587589b2805f71101972c801629cb3e016608; original global index 13009.
def localCycle00155 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle a8ba4ba1eaf3a815339f37378a9b944e38fd067c605b2604597cfb8278525120; original global index 13133.
def localCycle00156 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -3, 0, -1, 0, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, true, false, true, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 6 1, .triangle 7 0, .triangle 28 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .thetaLower 1]

-- Original cycle a9707215f99a8e69d5fcd6ef958d61def534f35a301e1e20c240afc21aadd29c; original global index 13190.
def localCycle00157 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 3 6, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 33 1]

-- Original cycle aa1913b317ac6d7198c5f2cd447c8e394067bcaa8bbb3bb440236abbaea50cc6; original global index 13243.
def localCycle00158 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle ace3599dcdd7e25dd87a3ba18d61bd46bda448a4d710a40e4cce7a75eed1f00f; original global index 13477.
def localCycle00159 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, 0, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 2, .triangle 8 1, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle ad517816caf10aee7829e1407bea107dec2b415e55b702ee2cc7e01fae280f82; original global index 13511.
def localCycle00160 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 23 0, .triangle 16 1, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle b0a65d5ec74dc3d83775ae3456745dfc09969d4a1dace3929e4ec8d8240e7787; original global index 13793.
def localCycle00161 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 20 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle b5d0df18bf9c3b006e02f7c0da093e244134a4511b748642de2f2b7fab098efa; original global index 14205.
def localCycle00162 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![0, 0, 2, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.gapLower 2 2, .gapLower 5 1, .gapUpper 4 1, .gapLower 0 4]

-- Original cycle b6a21f6c9f37188b7ca520c86c4df96c6320748eee65964a7c5e7856313f90e5; original global index 14272.
def localCycle00163 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle b9615bdb3e9cbbc0f58bad2bd39867096cc15a6bf9dca9801cbf7d5f32d19e11; original global index 14466.
def localCycle00164 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 4 2, .gapLower 6 2, .corridorLower 2 6, .thetaLower 2]

-- Original cycle ba09a2cdd324b5b7e4e38bc4af6a4a09ae815fb771a8d87c570f9d30d24f6aad; original global index 14526.
def localCycle00165 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 3 6, .distance 2 6, .distance 0 2]
    constant := ![0, -2, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 8 2, .gapLower 6 3, .gapLower 6 2, .gapUpper 2 3]

-- Original cycle ba24c73c7f2e76525993f51339c671d8e0e32eb115e9ef7baca406b85d41ac32; original global index 14535.
def localCycle00166 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 26 1, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle ba2713ab6ee4fe0f24a2635ec4932be7843a73b9324cb0579ced4c943b183d51; original global index 14536.
def localCycle00167 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 3, .triangle 8 1, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle bbaaea7c6bebe6a66090c6181aabbbedf7bbbea3636d936d9f08b6f7f6bea8d3; original global index 14652.
def localCycle00168 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![4, 0, -2, -2, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 29 2, .gapLower 6 3, .gapLower 6 2, .triangle 11 1, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle bc3eb08a15981417d7e8a069c0b612e96ce6e8492749fca448aa6ac501f23752; original global index 14695.
def localCycle00169 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .gapLower 6 4, .gapLower 6 3, .triangle 8 1, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle bcbec31fd637ce9486a369bffec10b2dbce02f6f411827f251de3f9b994efe31; original global index 14724.
def localCycle00170 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 6 1, .triangle 7 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle bce49e1fc4310c10b3aa95d7d2ae57f664b6c43c30ed3661878386d634fba87e; original global index 14737.
def localCycle00171 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 29 1, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle bd1f6a4f13b3883eacb565b0b4f480037c1228d2e4e0a5dba89937c7104fcfe0; original global index 14755.
def localCycle00172 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 16 0, .triangle 29 0, .triangle 34 1, .triangle 14 0, .triangle 7 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle bd7e9656b5159af002e0b04971df3863b0745475f2cf91e7fb82e4424a9c9ffc; original global index 14781.
def localCycle00173 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 1 6, .distance 1 2]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 4, .gapLower 6 3, .triangle 18 1]

-- Original cycle be9863cd5aaa136c7668602670e3ed15f5ee7e9c548850393cf3c64ffba80fd6; original global index 14869.
def localCycle00174 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 2, .triangle 11 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle bf8878f22b2a459ad7128e60c1497d71c90fb9e201f15c139539ef95c6779947; original global index 14945.
def localCycle00175 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 3 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 4, .triangle 11 2, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle c0439ea787214725ca3d8f00d30feaaac8ca774a73ab25769dabd0854d1e9743; original global index 15011.
def localCycle00176 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, -2, 0, 3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, -1, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapUpper 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c0ba258885c2250e08625289fef370ba149b18b8d58cd6914998e7a651c1f545; original global index 15049.
def localCycle00177 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle c335b0ac827b41ce39baa6a6b11f6f0e06b5a6abd579143f47a9bce802182418; original global index 15231.
def localCycle00178 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 4, .triangle 11 1, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle c350338fe75668cb7597d652a114f402b149203bbeac4c4a4130e502993ed282; original global index 15237.
def localCycle00179 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 30 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle c369e6150391e8520e03cebfd00ee43486eb6a410efd018a51a9831963cd490e; original global index 15251.
def localCycle00180 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle c39c4aa5c3fa5521cf89c17c68eca7ff264fa67c5f226d95c32465b0064183fa; original global index 15268.
def localCycle00181 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c4aa4ea1cf8761847a8343b8219a92f01ff5ba74b7329780069befd49f58d85e; original global index 15337.
def localCycle00182 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c610d7abf406ec57b70c18a4a4fde3bb3875a887da8cceb95f77ebbb092cc65d; original global index 15448.
def localCycle00183 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 3 2, .gapLower 0 1]

-- Original cycle c714f51358e9548d6ec3e2728559da1072560b8f6a9af9c57194cba5c9173a43; original global index 15535.
def localCycle00184 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 4, .triangle 11 1, .triangle 27 2, .triangle 29 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle c7a0bb2205ce17b7742ecb4808da8b912a786cee9568f1f47d977231124820cd; original global index 15580.
def localCycle00185 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c7ee013a7502bf2f19cf7c639e12dd86bf97d394e8025f018c70cd231d379c1d; original global index 15608.
def localCycle00186 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 24 0, .gapLower 1 2]

-- Original cycle c8b1c7b7615040ef36f16be6c30b3097b807ed376c088a5e9bffc61822749c5c; original global index 15676.
def localCycle00187 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 3, .triangle 11 1, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c908652b7fae3e0cc37ba7e5838dc71352f531d2529a67b64bccf5b6c3ce5748; original global index 15702.
def localCycle00188 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .gapLower 6 3, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle ca044f438519ca1e2856b23d8b81df6187a4bdfa70a5fedf7454a4bfccfb73dd; original global index 15790.
def localCycle00189 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 29 1, .gapLower 6 0, .gapLower 6 6, .triangle 33 0, .triangle 20 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle ca61ebf6c0d5404d9f0f4b686621aa265296901bad0e31270abf7b9cdab8ea78; original global index 15819.
def localCycle00190 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 4 2, .gapLower 6 3, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle cb4ca35426ffc13c3db07e710765d6b9602a266cf0ec7c9b5c7113e0208c47eb; original global index 15879.
def localCycle00191 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 8 1, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle cc951b2be0490eae12dc06cbf94dd0efb54b2235da5aead9a4842ff4962f793e; original global index 15990.
def localCycle00192 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 16 0, .triangle 29 0, .triangle 13 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ccb0f35ca06f4fe8ad6d0a014ee3defa05e3c61cd2e3fb82c678cc689166e88c; original global index 16000.
def localCycle00193 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle cce94df71ec413f5f810be46f3dfc12e0926b743c0812129a4a87c318953442d; original global index 16014.
def localCycle00194 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle d0e7635d2b7ffce32a1db59d484835c1eb6fba7379dd37325baf35383933face; original global index 16314.
def localCycle00195 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 2, .triangle 6 1, .triangle 5 2, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle d3a70ef3bcd7e7f8ddbf979b6d89faa418128307626f5c04f031f2c4d8637117; original global index 16513.
def localCycle00196 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 26 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d3e789e085c7eadf6db6a9edf2c5a7c4dc63deed9b2bb2c78239ddd091944e0d; original global index 16540.
def localCycle00197 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 6 1, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle d52fc5ca41f9761b638a2755346bb5bc9c032adbec5fb812305e1c956f72341d; original global index 16638.
def localCycle00198 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 6 1, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle d8694a9b398ee8461bcad5c819950f4d61e6c9da397e11bad654245bcfff7390; original global index 16894.
def localCycle00199 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 6 1, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle d8f65fb81ad222569508b74a157a729bb35069e8556b6029ec2c2adb0245eba8; original global index 16945.
def localCycle00200 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 2, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle d9b13ebcd1a927d25013fd0de3ba49cb90def5888962190272bed01de7fa2322; original global index 17006.
def localCycle00201 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 3 6, .distance 2 6, .distance 0 2]
    constant := ![0, -2, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.triangle 8 2, .gapLower 6 3, .triangle 27 2, .gapUpper 2 3]

-- Original cycle dcdf4184bd5cd19b62bd16cc9723465064ac765caf4187d78ff20160dfc30ec0; original global index 17261.
def localCycle00202 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 4 2, .triangle 11 1, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle dcfbecfd1a9620b524ea4fc0fd2c22b6c82eac6c8236869301da51e2a5a4f468; original global index 17275.
def localCycle00203 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 8 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ddf7f99dcc4acfbac2873fc2507ebc2449f2bdc5711da42981a6af53567f59dd; original global index 17352.
def localCycle00204 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![0, 2, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false] }
  origin := ![.triangle 17 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 16 0]

-- Original cycle de5f761374a630e8403a02c90d440fd601768e629a2545dbfa0af8ee353a45a8; original global index 17384.
def localCycle00205 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 24 0, .gapLower 1 2]

-- Original cycle df745d064953901c9f6efbb6f9ef70280690627895fc3a127f7a1b4148d68215; original global index 17461.
def localCycle00206 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -3, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 6 2, .triangle 11 1, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle e03dba408f676bd864a0f60db06b239f623c5b325e9fefbcc75437a842acf085; original global index 17529.
def localCycle00207 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle e1c35541fd67e6a781017d02b67f9441e5bee57548d5a516797f676e30d38b0d; original global index 17652.
def localCycle00208 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 0 2, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle e3bb372fcaef8247878717490c8f26bc94ed1f985ca2a550f0d269b1906481de; original global index 17808.
def localCycle00209 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 1 6, .distance 1 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 4, .gapLower 6 4, .triangle 24 1]

-- Original cycle e51892bee8e532149f3a54333cb13593e8fd84348808a66fda3c83758d84839b; original global index 17909.
def localCycle00210 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -2, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 2, .triangle 21 0, .gapLower 6 3, .triangle 8 1, .triangle 29 1, .triangle 34 1, .gapLower 4 0]

-- Original cycle e743b5d74cd80a53a91d62e047310312b99c5b5954d365ff07f92fbd3ef6cb56; original global index 18090.
def localCycle00211 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 18 2, .gapLower 6 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle e84bcb291ac6a061c906ce686a9032e111261e12d87ad2365a28c26038ef7a5e; original global index 18160.
def localCycle00212 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, -2, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 2, .triangle 8 1, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle e8710b29665a723aaadc37ae8a00eecd76dc97ccb842f1f7dd12523ad834d86d; original global index 18170.
def localCycle00213 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 0 2, .triangle 5 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle e8985881412f38727510ff96029901b319f7609463b30071f5d409517c06919f; original global index 18182.
def localCycle00214 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .theta 6, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, 2, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 29 1, .gapLower 6 0, .gapLower 6 6, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle e9b8c9075c6db4f5b75f0f1afaca90fcdd8b6ade96e6b088ef8b54fbdae00754; original global index 18263.
def localCycle00215 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![-2, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 5 2, .triangle 28 1, .gapUpper 4 1, .gapLower 0 4]

-- Original cycle ebab08c0ce8fe9df9550f71ba6de576de89682a62e8df21ab7b5c3e119ecaa05; original global index 18390.
def localCycle00216 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ed203cb8589e1a1de944b8cd44ec43518a0dae0f15fbaf378846f6a4ac22df18; original global index 18513.
def localCycle00217 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .triangle 18 2, .gapLower 6 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle edb87115ee5ad585f48dd4caae0a36c2509de3fa15deb863196670ce9d825593; original global index 18558.
def localCycle00218 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ee4bed3390fae9ea600c14c36613854832ff0b2633ac942d61997e33c9e9256f; original global index 18598.
def localCycle00219 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 21 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle f093c50e8582e877810b82eade3eb4e8821e5abd507fd49e8bda751db8096084; original global index 18758.
def localCycle00220 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 3 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![0, 2, 2, -2, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.gapLower 1 3, .gapUpper 5 4, .gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 18 0]

-- Original cycle f14c40b916271c95d300e4f3346cf5c7f12b12a9dcdca2f4cb4519a4abf4edb4; original global index 18815.
def localCycle00221 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 3 2, .gapLower 0 1]

-- Original cycle f3f36aa99721690ddb169e61aadce8c1784982cda8622000f8516034be75b3c4; original global index 19024.
def localCycle00222 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .triangle 8 1, .triangle 29 1, .gapLower 6 0]

-- Original cycle f542610fe57ef15ad08179af166667c3c69fd5801340561a977b2a91ee064a92; original global index 19117.
def localCycle00223 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle f59f1e2aac64b16c9d4fe2112acc2ec7ee610d2cb485fdc0a4c220ea6b6e414c; original global index 19151.
def localCycle00224 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 4, .triangle 27 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle f9fa0f25871929d20f71711e55e5c3f8fb50861c2a628bc0e1d8f3fe6b1c1df8; original global index 19492.
def localCycle00225 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![-1, 0, 2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.triangle 7 0, .triangle 28 1, .gapUpper 4 1, .gapLower 0 4]

-- Original cycle fa238d071ab80125a386d17edc22ea9934653beb4682796c2d8ef3090af8060a; original global index 19503.
def localCycle00226 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 29 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle fa8b43ac774cfb18a7310439dab6010d8d1636ff7c7023daf50d70a49645a61e; original global index 19546.
def localCycle00227 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 6 0, .triangle 7 2, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle fab05210c4ac1e2c6b08ece15566990d62e66fbe93007723cae5cab4f97f272e; original global index 19558.
def localCycle00228 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Original cycle fbbeef991e6ddeaacc1ddf1126cb96343fc3119439a6afd1cd7ffd5a7acaed18; original global index 19653.
def localCycle00229 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 1, .triangle 24 0, .triangle 20 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle fd036196c8e7390925e8d853de082a3977f380e2343bb3335ceaaed64c716ac1; original global index 19773.
def localCycle00230 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, 0, -2, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, true, false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 6 1, .triangle 7 2, .gapLower 0 2, .gapLower 3 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

def library : Library := fun id => if id < 115 then (if id < 57 then (if id < 28 then (if id < 14 then (if id < 7 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 5 then (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)) else (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)))) else (if id < 10 then (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))) else (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none))))) else (if id < 21 then (if id < 17 then (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none))) else (if id < 19 then (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)))) else (if id < 24 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none))) else (if id < 26 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none)))))) else (if id < 42 then (if id < 35 then (if id < 31 then (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none))) else (if id < 33 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none)) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)))) else (if id < 38 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none))) else (if id < 40 then (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none)) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))))) else (if id < 49 then (if id < 45 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))) else (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)))) else (if id < 53 then (if id < 51 then (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none)) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none))) else (if id < 55 then (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none))))))) else (if id < 86 then (if id < 71 then (if id < 64 then (if id < 60 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 62 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none)) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none)))) else (if id < 67 then (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none))) else (if id < 69 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))))) else (if id < 78 then (if id < 74 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none))) else (if id < 76 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)))) else (if id < 82 then (if id < 80 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none))) else (if id < 84 then (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)))))) else (if id < 100 then (if id < 93 then (if id < 89 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none))) else (if id < 91 then (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none)) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none)))) else (if id < 96 then (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none))) else (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none))))) else (if id < 107 then (if id < 103 then (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none))) else (if id < 105 then (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)))) else (if id < 111 then (if id < 109 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none))) else (if id < 113 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none)) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none)))))))) else (if id < 173 then (if id < 144 then (if id < 129 then (if id < 122 then (if id < 118 then (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none))) else (if id < 120 then (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)))) else (if id < 125 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none))) else (if id < 127 then (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none)) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none))))) else (if id < 136 then (if id < 132 then (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none))) else (if id < 134 then (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none)) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none)))) else (if id < 140 then (if id < 138 then (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none)) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none))) else (if id < 142 then (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none)) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none)))))) else (if id < 158 then (if id < 151 then (if id < 147 then (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none))) else (if id < 149 then (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none)) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)))) else (if id < 154 then (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none))) else (if id < 156 then (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none)) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none))))) else (if id < 165 then (if id < 161 then (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none))) else (if id < 163 then (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none)) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none)))) else (if id < 169 then (if id < 167 then (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none)) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none))) else (if id < 171 then (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none)) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none))))))) else (if id < 202 then (if id < 187 then (if id < 180 then (if id < 176 then (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id = 175 then some localCycle00175 else none))) else (if id < 178 then (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none)) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none)))) else (if id < 183 then (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none))) else (if id < 185 then (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none)) else (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none))))) else (if id < 194 then (if id < 190 then (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none))) else (if id < 192 then (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id = 191 then some localCycle00191 else none)) else (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id = 193 then some localCycle00193 else none)))) else (if id < 198 then (if id < 196 then (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none)) else (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none))) else (if id < 200 then (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none)) else (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none)))))) else (if id < 216 then (if id < 209 then (if id < 205 then (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id = 204 then some localCycle00204 else none))) else (if id < 207 then (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id = 206 then some localCycle00206 else none)) else (if id < 208 then (if id = 207 then some localCycle00207 else none) else (if id = 208 then some localCycle00208 else none)))) else (if id < 212 then (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id = 211 then some localCycle00211 else none))) else (if id < 214 then (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id = 213 then some localCycle00213 else none)) else (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none))))) else (if id < 223 then (if id < 219 then (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id = 218 then some localCycle00218 else none))) else (if id < 221 then (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id = 220 then some localCycle00220 else none)) else (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id = 222 then some localCycle00222 else none)))) else (if id < 227 then (if id < 225 then (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id = 224 then some localCycle00224 else none)) else (if id < 226 then (if id = 225 then some localCycle00225 else none) else (if id = 226 then some localCycle00226 else none))) else (if id < 229 then (if id < 228 then (if id = 227 then some localCycle00227 else none) else (if id = 228 then some localCycle00228 else none)) else (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id = 230 then some localCycle00230 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 5, 3, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 6, 0, 5, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 3, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 8 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4608)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 5, 3, 2, 4], ![6, 3, 0, 5, 1, 4], ![6, 2, 0, 5, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 3, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 29 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4609)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 3, 5, 2, 4, 6], ![3, 5, 0, 1, 4, 6], ![2, 0, 1, 5, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 2, 0, 1, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .low0 (![30, 183, 145, 119, 162, 156, 51, 221, 34, 144, 0, 150, 150, 115, 221, 225, 221, 221, 138, 225, 230, 227, 215, 69, 2, 225, 0, 170]) }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4610)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 3, 5, 2, 4, 6], ![3, 5, 0, 1, 4, 6], ![2, 0, 1, 5, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 2, 0, 1, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 11 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4611)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 3, 5, 2, 4, 6], ![3, 5, 0, 1, 4, 6], ![2, 0, 1, 6, 5, 4], ![5, 0, 1, 2, 6, 3], ![4, 2, 0, 1, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 208 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4612)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 3, 5, 2, 4, 6], ![3, 5, 0, 1, 6, 4], ![2, 0, 1, 5, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 2, 0, 1, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 17 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4613)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 3, 5, 2, 6, 4], ![3, 5, 0, 1, 6, 4], ![2, 0, 1, 5, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 0, 1, 3, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 198 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4614)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 3, 5, 6, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 1, 5, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 0, 1, 3, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 4 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4615)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 3, 5, 2, 4, 6], ![3, 5, 0, 1, 6, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 1, 6, 2, 3], ![4, 2, 0, 1, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 98 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4616)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 3, 5, 2, 6, 4], ![3, 5, 0, 1, 6, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 0, 1, 6, 3], ![0, 4, 1, 2, 5, 3]], proof := .tail 199 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4617)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 3, 5, 6, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 0, 1, 6, 3], ![0, 4, 2, 1, 5, 3]], proof := .tail 4 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4618)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 3, 6, 5, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 0, 6, 1, 3], ![0, 4, 2, 5, 1, 3]], proof := .tail 179 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4619)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 6, 3, 5, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 6, 1, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 0, 6, 1, 3], ![0, 4, 2, 5, 3, 1]], proof := .tail 137 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4620)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 3, 5, 2, 6, 4], ![0, 3, 5, 2, 6, 4], ![3, 5, 0, 1, 6, 4], ![2, 0, 1, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 1, 3, 6], ![4, 0, 1, 2, 3, 5]], proof := .low6 (![58, 42, 89, 173, 99, 157, 5, 60, 217, 140, 59, 101, 161, 211, 130, 75, 122, 161, 129, 159, 219, 45, 212, 33, 158, 220, 59, 53]) }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4621)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 3, 5, 2, 6, 4], ![0, 3, 5, 2, 6, 4], ![3, 5, 0, 1, 6, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 1, 6, 3], ![4, 0, 1, 2, 5, 3]], proof := .tail 84 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4622)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 3, 5, 2, 6, 4], ![0, 3, 5, 6, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 1, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 1, 3, 6], ![4, 0, 2, 1, 3, 5]], proof := .tail 4 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4623)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 3, 5, 2, 6, 4], ![0, 3, 5, 6, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 1, 6, 3], ![4, 0, 2, 1, 5, 3]], proof := .tail 4 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4624)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 3, 5, 2, 6, 4], ![0, 3, 6, 5, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 6, 1, 3], ![4, 0, 2, 5, 1, 3]], proof := .tail 179 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4625)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 3, 5, 2, 6, 4], ![0, 6, 3, 5, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 6, 1, 3], ![4, 0, 2, 5, 3, 1]], proof := .tail 137 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4626)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 3, 5, 6, 2, 4], ![0, 3, 5, 6, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 0, 1, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 1, 3, 6], ![4, 2, 0, 1, 3, 5]], proof := .low6 (![147, 16, 78, 167, 141, 157, 5, 9, 120, 88, 222, 14, 189, 7, 92, 106, 136, 136, 1, 127, 121, 161, 191, 44, 161, 76, 91, 53]) }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4627)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 3, 5, 6, 2, 4], ![0, 3, 5, 6, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 1, 6, 3], ![4, 2, 0, 1, 5, 3]], proof := .low6 (![147, 16, 78, 167, 209, 186, 229, 9, 120, 88, 35, 205, 94, 7, 92, 77, 205, 136, 1, 108, 205, 85, 169, 205, 13, 114, 41, 205]) }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4628)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 3, 5, 6, 2, 4], ![0, 3, 6, 5, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 6, 1, 3], ![4, 2, 0, 5, 1, 3]], proof := .tail 117 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4629)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 3, 6, 5, 2, 4], ![0, 3, 6, 5, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 6, 0, 1, 3], ![4, 2, 5, 0, 1, 3]], proof := .tail 223 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4630)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 3, 6, 5, 2, 4], ![0, 3, 6, 5, 2, 4], ![3, 6, 5, 0, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 0, 1, 3], ![4, 5, 2, 0, 1, 3]], proof := .tail 10 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4631)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 3, 6, 5, 2, 4], ![0, 3, 6, 5, 2, 4], ![3, 6, 5, 0, 1, 4], ![2, 0, 1, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 0, 1, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 100 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4632)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 3, 5, 6, 2, 4], ![0, 6, 3, 5, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 0, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 6, 1, 3], ![4, 2, 0, 5, 3, 1]], proof := .tail 48 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4633)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 3, 6, 5, 2, 4], ![0, 6, 3, 5, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 0, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 6, 0, 1, 3], ![4, 2, 5, 0, 3, 1]], proof := .tail 48 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4634)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 3, 6, 5, 2, 4], ![0, 6, 3, 5, 2, 4], ![3, 6, 5, 0, 1, 4], ![2, 0, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 0, 1, 3], ![4, 5, 2, 0, 3, 1]], proof := .tail 10 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4635)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 3, 6, 5, 2, 4], ![0, 6, 3, 5, 2, 4], ![3, 6, 5, 0, 1, 4], ![2, 0, 6, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 0, 1, 3], ![5, 4, 2, 0, 3, 1]], proof := .tail 100 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4636)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 6, 3, 5, 2, 4], ![0, 6, 3, 5, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 6, 0, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 6, 0, 1, 3], ![4, 2, 5, 3, 0, 1]], proof := .tail 111 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4637)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 6, 3, 5, 2, 4], ![0, 6, 3, 5, 2, 4], ![3, 6, 5, 0, 1, 4], ![2, 6, 0, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 0, 1, 3], ![4, 5, 2, 3, 0, 1]], proof := .tail 10 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4638)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 6, 3, 5, 2, 4], ![0, 6, 3, 5, 2, 4], ![3, 6, 5, 0, 1, 4], ![2, 6, 0, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 0, 1, 3], ![5, 4, 2, 3, 0, 1]], proof := .tail 100 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4639)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 6, 3, 5, 2, 4], ![0, 6, 3, 5, 2, 4], ![6, 3, 5, 0, 1, 4], ![6, 2, 0, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 0, 1, 3], ![4, 5, 3, 2, 0, 1]], proof := .tail 166 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4640)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 6, 3, 5, 2, 4], ![0, 6, 3, 5, 2, 4], ![6, 3, 5, 0, 1, 4], ![6, 2, 0, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 0, 1, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 153 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4641)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 5, 3, 2, 4, 6], ![3, 5, 0, 1, 4, 6], ![2, 0, 5, 1, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 2, 0, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 204 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4642)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 5, 3, 2, 4, 6], ![3, 5, 0, 1, 4, 6], ![2, 0, 5, 1, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 2, 0, 3, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 27 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4643)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 5, 3, 2, 4, 6], ![3, 5, 0, 1, 6, 4], ![2, 0, 5, 1, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 2, 0, 3, 1, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 82 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4644)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 5, 3, 2, 6, 4], ![3, 5, 0, 1, 6, 4], ![2, 0, 5, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 0, 3, 1, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 198 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4645)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 5, 3, 6, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 5, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 0, 3, 1, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 4 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4646)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 5, 6, 3, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 5, 6, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 0, 3, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 180 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4647)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 6, 5, 3, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 5, 6, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 0, 3, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 179 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4648)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 3, 5, 2, 4, 6], ![0, 6, 5, 3, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 6, 5, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 0, 6, 3, 1], ![0, 4, 2, 5, 3, 1]], proof := .tail 124 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4649)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 3, 5, 2, 6, 4], ![0, 5, 3, 2, 6, 4], ![3, 5, 0, 1, 6, 4], ![2, 0, 5, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 3, 1, 6], ![4, 0, 1, 2, 3, 5]], proof := .low6 (![58, 42, 89, 173, 3, 46, 155, 60, 217, 140, 79, 54, 6, 211, 130, 79, 54, 6, 129, 79, 54, 193, 103, 86, 139, 146, 79, 54]) }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4650)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 3, 5, 2, 6, 4], ![0, 5, 3, 6, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 5, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 3, 1, 6], ![4, 0, 2, 1, 3, 5]], proof := .tail 4 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4651)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 3, 5, 2, 6, 4], ![0, 5, 6, 3, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 5, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 3, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 180 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4652)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 3, 5, 2, 6, 4], ![0, 6, 5, 3, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 5, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 3, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 179 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4653)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 3, 5, 2, 6, 4], ![0, 6, 5, 3, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 0, 6, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 6, 3, 1], ![4, 0, 2, 5, 3, 1]], proof := .tail 124 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4654)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 3, 5, 6, 2, 4], ![0, 5, 3, 6, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 0, 5, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 3, 1, 6], ![4, 2, 0, 1, 3, 5]], proof := .low6 (![147, 16, 78, 167, 104, 46, 181, 9, 120, 88, 152, 54, 151, 7, 92, 106, 54, 136, 1, 127, 54, 193, 191, 54, 193, 74, 64, 54]) }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4655)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 3, 5, 6, 2, 4], ![0, 5, 6, 3, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 0, 5, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 3, 1, 6], ![4, 2, 0, 3, 1, 5]], proof := .low6 (![61, 55, 25, 134, 109, 133, 96, 128, 154, 210, 97, 12, 40, 194, 52, 224, 57, 57, 188, 175, 164, 200, 149, 118, 118, 38, 70, 80]) }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4656)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 3, 5, 6, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 0, 5, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 3, 6, 1], ![4, 2, 0, 3, 5, 1]], proof := .tail 117 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4657)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 3, 5, 6, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 0, 6, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 0, 6, 3, 1], ![4, 2, 0, 5, 3, 1]], proof := .tail 124 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4658)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 3, 6, 5, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 0, 6, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 6, 0, 3, 1], ![4, 2, 5, 0, 3, 1]], proof := .tail 124 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4659)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 3, 6, 5, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 6, 5, 0, 1, 4], ![2, 0, 6, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 0, 3, 1], ![4, 5, 2, 0, 3, 1]], proof := .tail 71 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4660)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 3, 6, 5, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 6, 5, 0, 1, 4], ![2, 0, 6, 5, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 0, 3, 1], ![5, 4, 2, 0, 3, 1]], proof := .tail 177 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4661)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 6, 3, 5, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 6, 0, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 6, 0, 3, 1], ![4, 2, 5, 3, 0, 1]], proof := .tail 112 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4662)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 6, 3, 5, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 6, 5, 0, 1, 4], ![2, 6, 0, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 0, 3, 1], ![4, 5, 2, 3, 0, 1]], proof := .tail 142 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4663)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 6, 3, 5, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 6, 5, 0, 1, 4], ![2, 6, 0, 5, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 0, 3, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 8 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4664)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 6, 3, 5, 2, 4], ![0, 6, 5, 3, 2, 4], ![6, 3, 5, 0, 1, 4], ![6, 2, 0, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 0, 3, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 18 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4665)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 6, 3, 5, 2, 4], ![0, 6, 5, 3, 2, 4], ![6, 3, 5, 0, 1, 4], ![6, 2, 0, 5, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 0, 3, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 29 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4666)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 3, 2, 4, 6], ![3, 5, 0, 1, 4, 6], ![2, 5, 0, 1, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 2, 3, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 185 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4667)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 3, 2, 4, 6], ![3, 5, 0, 1, 4, 6], ![2, 5, 0, 1, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 2, 3, 0, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 27 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4668)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 3, 2, 4, 6], ![3, 5, 0, 1, 6, 4], ![2, 5, 0, 1, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 2, 3, 0, 1, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 195 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4669)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 3, 2, 6, 4], ![3, 5, 0, 1, 6, 4], ![2, 5, 0, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 3, 0, 1, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 20 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4670)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 3, 6, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 5, 0, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 3, 0, 1, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 87 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4671)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 6, 3, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 5, 0, 6, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 3, 0, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 148 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4672)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 6, 5, 3, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 5, 0, 6, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 3, 0, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 182 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4673)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 5, 3, 2, 6, 4], ![0, 5, 3, 2, 6, 4], ![3, 5, 0, 1, 6, 4], ![2, 5, 0, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 0, 1, 6], ![4, 0, 1, 2, 3, 5]], proof := .low6 (![58, 42, 206, 173, 3, 46, 181, 60, 217, 140, 79, 54, 126, 211, 130, 79, 54, 126, 168, 79, 54, 66, 103, 86, 68, 146, 79, 54]) }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4674)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 5, 3, 2, 6, 4], ![0, 5, 3, 6, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 5, 0, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 0, 1, 6], ![4, 0, 2, 1, 3, 5]], proof := .tail 87 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4675)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 5, 3, 2, 6, 4], ![0, 5, 6, 3, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 5, 0, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 0, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 148 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4676)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 5, 3, 2, 6, 4], ![0, 6, 5, 3, 2, 4], ![3, 5, 0, 6, 1, 4], ![2, 5, 0, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 0, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 182 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4677)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 5, 3, 6, 2, 4], ![0, 5, 3, 6, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 5, 0, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 0, 1, 6], ![4, 2, 0, 1, 3, 5]], proof := .low6 (![147, 16, 78, 125, 104, 46, 181, 9, 120, 187, 49, 54, 214, 7, 92, 106, 54, 136, 1, 127, 54, 207, 21, 54, 187, 74, 28, 54]) }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4678)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 5, 3, 6, 2, 4], ![0, 5, 6, 3, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 5, 0, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 0, 1, 6], ![4, 2, 0, 3, 1, 5]], proof := .tail 148 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4679)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 5, 3, 6, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 5, 0, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 0, 6, 1], ![4, 2, 0, 3, 5, 1]], proof := .tail 182 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4680)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 5, 6, 3, 2, 4], ![0, 5, 6, 3, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 5, 6, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 0, 1, 6], ![4, 2, 3, 0, 1, 5]], proof := .low6 (![67, 113, 63, 56, 83, 133, 176, 131, 22, 201, 184, 226, 226, 22, 26, 62, 95, 95, 165, 178, 107, 107, 19, 190, 201, 110, 65, 202]) }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4681)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 5, 6, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 5, 6, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 0, 6, 1], ![4, 2, 3, 0, 5, 1]], proof := .tail 117 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4682)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 5, 6, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 6, 0, 1], ![4, 2, 3, 5, 0, 1]], proof := .tail 223 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4683)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 5, 6, 0, 1, 4], ![2, 6, 5, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 6, 3, 0, 1], ![4, 2, 5, 3, 0, 1]], proof := .tail 81 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4684)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 6, 5, 0, 1, 4], ![2, 6, 5, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 3, 0, 1], ![4, 5, 2, 3, 0, 1]], proof := .tail 90 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4685)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![3, 6, 5, 0, 1, 4], ![2, 6, 5, 0, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 3, 0, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 43 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4686)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![6, 3, 5, 0, 1, 4], ![6, 2, 5, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 3, 0, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 73 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4687)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![6, 3, 5, 0, 1, 4], ![6, 2, 5, 0, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 3, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 123 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4688)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 3, 2, 4, 6], ![5, 3, 0, 1, 4, 6], ![5, 2, 0, 1, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 3, 2, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 228 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4689)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 3, 2, 4, 6], ![5, 3, 0, 1, 4, 6], ![5, 2, 0, 1, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 3, 2, 0, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 47 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4690)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 3, 2, 4, 6], ![5, 3, 0, 1, 6, 4], ![5, 2, 0, 1, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 3, 2, 0, 1, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 135 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4691)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 3, 2, 6, 4], ![5, 3, 0, 1, 6, 4], ![5, 2, 0, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 2, 0, 1, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 197 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4692)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 3, 6, 2, 4], ![5, 3, 0, 6, 1, 4], ![5, 2, 0, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 2, 0, 1, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 39 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4693)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 6, 3, 2, 4], ![5, 3, 0, 6, 1, 4], ![5, 2, 0, 6, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 2, 0, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 36 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4694)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 6, 5, 3, 2, 4], ![5, 3, 0, 6, 1, 4], ![5, 2, 0, 6, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 2, 0, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 24 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4695)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 5, 3, 2, 6, 4], ![0, 5, 3, 2, 6, 4], ![5, 3, 0, 1, 6, 4], ![5, 2, 0, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 0, 1, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 163 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4696)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 5, 3, 2, 6, 4], ![0, 5, 3, 6, 2, 4], ![5, 3, 0, 6, 1, 4], ![5, 2, 0, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 0, 1, 6], ![4, 0, 2, 1, 3, 5]], proof := .tail 39 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4697)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 5, 3, 2, 6, 4], ![0, 5, 6, 3, 2, 4], ![5, 3, 0, 6, 1, 4], ![5, 2, 0, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 0, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 36 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4698)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 5, 3, 2, 6, 4], ![0, 6, 5, 3, 2, 4], ![5, 3, 0, 6, 1, 4], ![5, 2, 0, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 0, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 24 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4699)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 5, 3, 6, 2, 4], ![0, 5, 3, 6, 2, 4], ![5, 3, 6, 0, 1, 4], ![5, 2, 0, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 0, 1, 6], ![4, 2, 0, 1, 3, 5]], proof := .tail 132 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4700)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 5, 3, 6, 2, 4], ![0, 5, 6, 3, 2, 4], ![5, 3, 6, 0, 1, 4], ![5, 2, 0, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 0, 1, 6], ![4, 2, 0, 3, 1, 5]], proof := .tail 93 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4701)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 5, 3, 6, 2, 4], ![0, 6, 5, 3, 2, 4], ![5, 3, 6, 0, 1, 4], ![5, 2, 0, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 0, 6, 1], ![4, 2, 0, 3, 5, 1]], proof := .tail 24 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4702)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 5, 6, 3, 2, 4], ![0, 5, 6, 3, 2, 4], ![5, 3, 6, 0, 1, 4], ![5, 2, 6, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 0, 1, 6], ![4, 2, 3, 0, 1, 5]], proof := .tail 174 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4703)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 5, 6, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![5, 3, 6, 0, 1, 4], ![5, 2, 6, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 0, 6, 1], ![4, 2, 3, 0, 5, 1]], proof := .tail 24 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4704)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![5, 3, 6, 0, 1, 4], ![5, 2, 6, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 6, 0, 1], ![4, 2, 3, 5, 0, 1]], proof := .tail 50 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4705)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 5, 6, 3, 2, 4], ![0, 5, 6, 3, 2, 4], ![5, 6, 3, 0, 1, 4], ![5, 6, 2, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 5]], proof := .tail 213 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4706)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 5, 6, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![5, 6, 3, 0, 1, 4], ![5, 6, 2, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 5, 1]], proof := .tail 117 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4707)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![5, 6, 3, 0, 1, 4], ![5, 6, 2, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 6, 0, 1], ![4, 3, 2, 5, 0, 1]], proof := .tail 223 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4708)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![6, 5, 3, 0, 1, 4], ![5, 6, 2, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 6, 2, 0, 1], ![4, 3, 5, 2, 0, 1]], proof := .tail 10 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4709)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![6, 5, 3, 0, 1, 4], ![6, 5, 2, 0, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 3, 2, 0, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 23 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4710)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 2, 4], ![6, 5, 3, 0, 1, 4], ![6, 5, 2, 0, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 3, 2, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 196 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4711)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 4, 2, 5, 6], ![3, 0, 4, 1, 5, 6], ![2, 0, 1, 4, 5, 6], ![0, 2, 1, 3, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 216 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4712)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 4, 2, 5, 6], ![3, 0, 4, 1, 5, 6], ![2, 0, 1, 4, 5, 6], ![0, 2, 1, 3, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 143 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4713)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 4, 2, 5, 6], ![3, 0, 4, 1, 5, 6], ![2, 0, 1, 4, 6, 5], ![0, 2, 1, 3, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 218 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4714)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 4, 2, 5, 6], ![3, 0, 4, 1, 6, 5], ![2, 0, 1, 4, 6, 5], ![0, 2, 1, 3, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 37 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4715)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 4, 2, 6, 5], ![3, 0, 4, 1, 6, 5], ![2, 0, 1, 4, 6, 5], ![0, 2, 1, 3, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .tail 15 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4716)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 4, 2, 5, 6], ![3, 0, 4, 1, 5, 6], ![2, 0, 1, 6, 4, 5], ![0, 2, 1, 6, 3, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 4, 3]], proof := .tail 72 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4717)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 4, 2, 5, 6], ![3, 0, 4, 1, 6, 5], ![2, 0, 1, 6, 4, 5], ![0, 2, 1, 6, 3, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 4, 3]], proof := .tail 116 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4718)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 4, 2, 6, 5], ![3, 0, 4, 1, 6, 5], ![2, 0, 1, 6, 4, 5], ![0, 2, 1, 6, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 4, 3]], proof := .tail 105 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4719)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 4, 6, 2, 5], ![3, 0, 4, 6, 1, 5], ![2, 0, 1, 4, 6, 5], ![0, 2, 1, 3, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 171 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4720)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 4, 6, 2, 5], ![3, 0, 4, 6, 1, 5], ![2, 0, 1, 6, 4, 5], ![0, 2, 1, 6, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 1, 4, 3]], proof := .tail 160 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4721)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 6, 4, 2, 5], ![3, 0, 4, 6, 1, 5], ![2, 0, 1, 6, 4, 5], ![0, 2, 6, 1, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 4, 1, 3]], proof := .tail 102 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4722)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 6, 4, 2, 5], ![3, 0, 6, 4, 1, 5], ![2, 0, 1, 6, 4, 5], ![0, 6, 2, 1, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 2, 1, 3]], proof := .tail 172 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4723)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 3, 4, 2, 5], ![3, 0, 4, 6, 1, 5], ![2, 0, 6, 1, 4, 5], ![0, 2, 6, 1, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 4, 3, 1]], proof := .tail 31 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4724)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 3, 4, 2, 5], ![3, 0, 6, 4, 1, 5], ![2, 0, 6, 1, 4, 5], ![0, 6, 2, 1, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 2, 3, 1]], proof := .tail 172 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4725)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 4, 2, 6, 5], ![3, 0, 4, 1, 6, 5], ![2, 0, 1, 4, 6, 5], ![0, 2, 1, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 15 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4726)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 4, 2, 6, 5], ![3, 0, 4, 1, 6, 5], ![2, 0, 1, 6, 4, 5], ![0, 2, 1, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 4, 3]], proof := .tail 105 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4727)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 4, 6, 2, 5], ![3, 0, 4, 6, 1, 5], ![2, 0, 1, 4, 6, 5], ![0, 2, 1, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .tail 171 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4728)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 4, 6, 2, 5], ![3, 0, 4, 6, 1, 5], ![2, 0, 1, 6, 4, 5], ![0, 2, 1, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 1, 4, 3]], proof := .tail 160 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4729)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 6, 4, 2, 5], ![3, 0, 4, 6, 1, 5], ![2, 0, 1, 6, 4, 5], ![0, 2, 6, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 4, 1, 3]], proof := .tail 102 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4730)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 6, 4, 2, 5], ![3, 0, 6, 4, 1, 5], ![2, 0, 1, 6, 4, 5], ![0, 6, 2, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 2, 1, 3]], proof := .tail 192 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4731)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 6, 3, 4, 2, 5], ![3, 0, 4, 6, 1, 5], ![2, 0, 6, 1, 4, 5], ![0, 2, 6, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 4, 3, 1]], proof := .tail 31 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4732)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 6, 3, 4, 2, 5], ![3, 0, 6, 4, 1, 5], ![2, 0, 6, 1, 4, 5], ![0, 6, 2, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 2, 3, 1]], proof := .tail 192 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4733)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 3, 6, 4, 2, 5], ![3, 0, 6, 4, 1, 5], ![2, 0, 1, 6, 4, 5], ![6, 0, 2, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 0, 2, 1, 3]], proof := .tail 203 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4734)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 6, 3, 4, 2, 5], ![3, 0, 6, 4, 1, 5], ![2, 0, 6, 1, 4, 5], ![6, 0, 2, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 0, 2, 3, 1]], proof := .tail 32 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4735)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (4608 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 4608 ≤ id.val) (hhigh : id.val < 4736) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 4608)) = true := by
  let j : Fin 128 := ⟨id.val - 4608, by omega⟩
  have hsum : 4608 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (4608 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard036
