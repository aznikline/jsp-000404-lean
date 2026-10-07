import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard013
open N4R2RowDataReplay

-- Original cycle 000f43faa11f7d4e3e8347d9f5e2de475acb2aca38b06d3e6f93f05bfa143003; original global index 5.
def localCycle00000 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 2 6]

-- Original cycle 005022a605258247ef82b7adb88b9bd597b824047de01ff27f60c035f65254af; original global index 29.
def localCycle00001 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 2 6, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 18 1, .triangle 27 1, .triangle 26 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 0099abeb46e32411b6d42e4c56455e24502edc63d41478bd234f50dae07c21b6; original global index 54.
def localCycle00002 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 0, .triangle 25 1, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 014deae4dd1836efa7d6f53f639ef6c4550a093e1f493d78f2571067ac0dfa1d; original global index 110.
def localCycle00003 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .gapLower 6 3, .triangle 13 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 01901196c566982c5803bcfd53ea7646e38f8b6ab016cef74ef0503443ed388f; original global index 132.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 29 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Original cycle 024dc887b2c28e308119d5af044d1af43e11c1c2ab6a260b30416f629ed9f149; original global index 184.
def localCycle00005 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 031aa33f5ab8d4436e30a71abb2765b44b6b4fcb6728be66dc34f53ddc5e4230; original global index 253.
def localCycle00006 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 6 5, .triangle 18 0]

-- Original cycle 03bfc20c5a176daf5a88bb93d858a6e79bd92bf5d4835b495e91932e9a6b4b73; original global index 304.
def localCycle00007 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 6, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .triangle 14 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Original cycle 04bea6034296f11ad9d823b34896d74d633c1a9eda23cb8b42aa9a582c29ecb9; original global index 381.
def localCycle00008 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .gapLower 6 3, .triangle 13 1, .corridorLower 4 6]

-- Original cycle 069975c9feed0d727a3801386b44ab86b8fa3da4ad1e671aa6f983665840cdd1; original global index 543.
def localCycle00009 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 0714da0d1293dcd27adde15b475c5d07e55649c0f6bd7e9ca8c9122a715c268b; original global index 582.
def localCycle00010 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 072a08b905b5add19b8b8e830438fd390bfdbc83ed205c05f2f9b9dca0f13df5; original global index 593.
def localCycle00011 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .triangle 18 2, .gapLower 6 3, .triangle 13 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 07fa26d683045916cf82496c6a91e11e7309de9a4818d9c9032e009dcb2f3d79; original global index 644.
def localCycle00012 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 0, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 0834bcb07ae67b42fc6fdd38b5e89fafa12f52033c2a72b2439bbcfb537b81ec; original global index 656.
def localCycle00013 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 2 6, .distance 2 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 27 1]

-- Original cycle 0a6b47893c82e7374a608ee743f76cd7e8eb6d203d36f28ecba78a1502470627; original global index 829.
def localCycle00014 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 0c4466f033ed88c86f9be0ad926d43a337f75e96790b0fee006f758cbd1d2417; original global index 968.
def localCycle00015 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 21 2, .gapLower 6 3, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 0cb0ddbe022a8fd82866bf1937b76a7377e86afdc82be627fc6c489fb72b0d94; original global index 1005.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 3 2, .triangle 14 2, .gapLower 6 2, .triangle 34 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 0ce2d72e4aa7d88a12947e458bd1e0b89ae3265902ebbaa383f2caadf32c01d3; original global index 1016.
def localCycle00017 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle 0d68b5eb83a7ce3da2a8aa401cf5d9f0ac3d1df1916727f9106dd86b3d80691a; original global index 1060.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, 0, -3, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .triangle 18 2, .gapLower 6 3, .triangle 14 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 0e0dcf95a94e86b464f51fadd03fb3b76364e7e9c5a5eba6a1f40b2969a49660; original global index 1104.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Original cycle 0e3ba0e05981e2b69f62046d3d16ceaad7a03dc4fb47bab8703b4d9bcaba8c88; original global index 1122.
def localCycle00020 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 1, .gapLower 6 3, .triangle 11 1]

-- Original cycle 0e7d6162e60b0730aaa1a85b787e3873c87d3e98566a99802491137ab3f4d1f2; original global index 1145.
def localCycle00021 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 0f2cc5a113debe551fec3d6336a40a235737ec79920442290d99f9fb394bd05d; original global index 1211.
def localCycle00022 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 0f3673090e4a0fbeeb52c21c6d468ca87ac8946e2beb1e975e40cb6060fb1ce8; original global index 1214.
def localCycle00023 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 10 2, .triangle 12 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 0f5f8b157c04abfa4714b927429ea9dd6234e98bf7a251851f5b823cd3a2ea0d; original global index 1221.
def localCycle00024 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 102545240abcb6a255b9ca10f4b917b1c7632a379dd802b84acf62421abc05d4; original global index 1297.
def localCycle00025 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 3 6, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -2, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 18 2, .gapLower 6 4, .triangle 11 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 10d2b9a510d02ddc2b1f07ab0e1ebad62d4aa5e85c5e496beacbebfb69c20495; original global index 1348.
def localCycle00026 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .gapLower 6 4, .triangle 4 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 10ea229f90330b3d111e2b6096cd58ed680919042a82a2d07c6c29db5587d16e; original global index 1357.
def localCycle00027 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .gapLower 6 4, .triangle 21 1, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 111a2c01b9baeaa9cf7436c5e3934a4ca297bd3aabfa0ae56a7f5f86f47162db; original global index 1365.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 113e6edf5185083f5ea3caf88b0884598f8fdd89b5dfa32d114f967659f5031a; original global index 1369.
def localCycle00029 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 1210373bebb66e41c06695f34397571f0bdc5512fe1e8f8a06eea6da67dee864; original global index 1442.
def localCycle00030 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 0 4]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 12 2, .triangle 14 0, .gapLower 6 1, .gapUpper 4 2]

-- Original cycle 124ac3e5c40d3ed807105791364b31aaa2681a4cdfd5dff51b6a422412475137; original global index 1454.
def localCycle00031 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 1 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 23 2, .gapLower 6 3, .triangle 8 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 1380958839af21a9214ebf797dd1c088d473104f72f1831c92af4e05252a0b24; original global index 1537.
def localCycle00032 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .triangle 13 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 140ea73ddc52aa3239b41f9173dfd2511fa00d6694285f6cf76523e98a104e09; original global index 1582.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 14ffec48bcf7749a94e505c416901be886eb519ca1faa02b31d8a3cf95a5a0d1; original global index 1665.
def localCycle00034 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 4 6, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 1, .gapLower 6 1, .triangle 34 1]

-- Original cycle 15960122bcabedf3b226882205c633d04e9415bbd93e909af336bc4cb32aad9c; original global index 1710.
def localCycle00035 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 2 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -3, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 29 2, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 15d6def44b2b6625751a3c961a2d33d82f7c202865548ee719b363e45f8daf10; original global index 1732.
def localCycle00036 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 3 5, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 31 2, .triangle 10 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 16c6a7253d9c6ee026b5f587e9e42fc13b5791766f2721f798d0a80316f3116a; original global index 1787.
def localCycle00037 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 2 3, .distance 2 6, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 25 1, .triangle 27 2, .gapLower 6 3, .corridorLower 3 6, .thetaNext 2]

-- Original cycle 16ee5400237df087905d48eccdd440535b083d56fcd019e4d12664a8dcb22b9b; original global index 1803.
def localCycle00038 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .gapLower 4 0]

-- Original cycle 16f3c5303a307164afc021d2c8c257291fd68f74a50f454f84739da217ed9a65; original global index 1804.
def localCycle00039 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .gapLower 6 3, .triangle 13 1, .gapLower 4 0]

-- Original cycle 1708f68a4ed3db9534d61b7e32c71de39bd769ae98bad1ff01641078d9ec93c5; original global index 1813.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 5, .triangle 4 2, .triangle 13 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 181e6ad44a3244af8536f4097cf54417c964dc3369716934798e913efd73860c; original global index 1886.
def localCycle00041 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -1, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 12 0, .triangle 34 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 19316a9b73827c7f7958a4c3f6e6f1a7d751a558f0562affafe09db35811323f; original global index 1967.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 0, .triangle 24 2, .gapLower 6 3, .triangle 8 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 19b6c62075a6fde37e13ab31e8b9ad5bd7dd78b17fdb2308072e35e505ed3f88; original global index 2008.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 21 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 19e35c9bfa5f1db04edb54dcec46f43a4f35078e4981aaac35cdc353debea7b4; original global index 2021.
def localCycle00044 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 9 2, .triangle 13 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 1b177caed8f4bb6b1550ca2d8954e5c15b13a4d862479c5f0b3bd01c3023e24a; original global index 2093.
def localCycle00045 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 1d1f654826ede1874b71a66000a5983f190bb9984ba76dec400cfe481b2fcc88; original global index 2243.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 30 2, .triangle 8 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 1d486c1d3b7b2cb456bbba2777201100016f7b3d18c1e866e93b8a0931da00d7; original global index 2254.
def localCycle00047 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 18 2, .gapLower 6 3, .triangle 13 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 1d57445d879c1294093d4b38441e38d9012b4449f0c3a1d932c91035ea48cfc8; original global index 2257.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 4 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -2, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 29 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle 1d5bd4ea999553a96a45a5275b0d96768edf72903a3c9922423017b4400282b9; original global index 2260.
def localCycle00049 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle 1e986e59de2eee6d7d4f91dc97054d4fc69200b3149733e3f62d1231c9a9ac12; original global index 2348.
def localCycle00050 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 1ed9b5089426b83901c48d4fbc29913e2d8a210e0263d80f1b213d0ef168a3bc; original global index 2369.
def localCycle00051 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 222d98dde9d60665c368ab5dd33ecd0418d21d5f12b7683ec5fedf41701859d6; original global index 2617.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 28 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle 223c73ae8a4d1c22ff28187ba7455670d31b7ae7061823580e5cf5482d5d241b; original global index 2623.
def localCycle00053 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 24 1, .triangle 30 2, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 22fda38e0238708bd673c17927a0e54e5103cade2a4a4fac2bb18fc00a0d1e99; original global index 2685.
def localCycle00054 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 12 2, .triangle 14 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 253c18ea885b1555cfef27a84da0838d8216d72e9d34d25eebe1b5027f34bdc2; original global index 2861.
def localCycle00055 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .gapLower 6 3, .triangle 13 1, .corridorLower 4 6]

-- Original cycle 25671f91f6e70f85da07223085d49baf010cfa71886305f866e8b1b2cb802cbd; original global index 2877.
def localCycle00056 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 26200180412aebf5a962e308fe013e1243589288f46f4ec5c7d3d2675673239e; original global index 2920.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .gapLower 6 4, .triangle 18 1, .triangle 15 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 2798db3a160191dab3b8cb603afcc604d5a6b63411db0a7ea9f11e911e97e5a6; original global index 3026.
def localCycle00058 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 4, .distance 2 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5, .zero]
    constant := ![0, 3, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 0, .triangle 29 2, .gapLower 6 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5, .thetaLower 5]

-- Original cycle 28a7c4562a31484230f2628ecedf0b602e83e08819dcdb60dc41d9f7e72c5549; original global index 3111.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 2 6, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .gapLower 6 3, .triangle 27 1, .triangle 26 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 29b419966c09a13c5a7043e7cdd5589ca3fcfa7bb4a946d309c77829fbd53ae4; original global index 3182.
def localCycle00060 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 2a5e02c26e3e4bb66b97efd944f6c7cec38383ba6953d3ba462e2af7a0f9e841; original global index 3230.
def localCycle00061 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 13 2, .gapLower 6 1, .gapUpper 4 2]

-- Original cycle 2aa59bd67a9016760d57f06eacf5dfd7975f0103bc0d94926a02e8c71d9629c5; original global index 3244.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 2b02fb8bb55390b45e02fa12b3f517179fbf20d96fc9a6afb6bc123b546bdbbf; original global index 3282.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 28 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 2b23cbf9326aa8c98f3607075aa59c18a571926dcd5524c8c61900010a6dbaf8; original global index 3296.
def localCycle00064 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 4 6, .theta 6, .theta 5, .distance 3 5, .distance 1 5, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -2, 0, 3, 0, 0, -2, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 29 0, .gapLower 6 0, .thetaNext 5, .corridorUpper 3 5, .triangle 20 2, .triangle 24 2, .gapLower 6 4, .triangle 30 0, .gapLower 2 2, .corridorLower 2 3]

-- Original cycle 2e619e575e5faacaef3277f429d9af9df841691617f425c5fa964e64098ca096; original global index 3547.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 2e711ba68ff10dc4f929cfcd8e0c241952a9297f89e3c2f36e083580c44ccc67; original global index 3551.
def localCycle00066 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 1 3]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 21 0]

-- Original cycle 302472dc74571a31b3bc64280b2858572a1c0b8da832fe94205203708f84e037; original global index 3669.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 6 4, .gapLower 6 3, .triangle 13 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 3085eb19e59457ef4d06717ddf091d0fcd5d87ef6ea2e60a3136609c364cb487; original global index 3694.
def localCycle00068 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 3, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 30970da7f8f9310e2bda978d9a344be08b852e36b8a7bb363a98e4769544b506; original global index 3706.
def localCycle00069 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 3 5, .distance 5 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 0, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 30e6ce3a7a0bad9350fc1fd4f0ed82642044bdc0d0d27d84955bb60bc269c0b7; original global index 3729.
def localCycle00070 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .triangle 21 1]

-- Original cycle 327c695c2540c151ac03abe84c53385b56f1812339be6fcff4409c2438a4ef1f; original global index 3861.
def localCycle00071 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 34eb9a5b4b67e3f14ca12a85f31176ee4311843abbbfaa330b606505d6423464; original global index 4049.
def localCycle00072 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 18 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 35123bd7a5c4f587570e401b7f707372c5073bf8e3dfa8ef4977b866b12a8ddf; original global index 4059.
def localCycle00073 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Original cycle 368df2626ca45afa1a79b8eae932b2ba95e23423dce56dea6e2b868298b9f46d; original global index 4190.
def localCycle00074 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 21 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 36f24ce6597a830a020b487eb6687d389f38a024066309a71b9aad3ade76463a; original global index 4219.
def localCycle00075 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 1 3]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 21 0]

-- Original cycle 37285485124530ccc70ec42f4d682cf2f23682fc73015d2b9b763218714aa475; original global index 4233.
def localCycle00076 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 3759763457d3501a6f21ec0ca338adf664f8c76aedfd0157c176462fbe97491b; original global index 4253.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 38a0ac3a31918bdfdae4e5a84703ab9c5c63f2bda9712d4f2a560abe1548cac8; original global index 4355.
def localCycle00078 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 3b57ecf50cde5b0fdff3ec23878cc64d7717275dea6c185438b52ecbdaa5e8fa; original global index 4587.
def localCycle00079 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 14 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 3d2151293512b5b6c990e3380cde994137c114eb884534c387736364e3641b6d; original global index 4737.
def localCycle00080 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .triangle 13 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 3d300f514691a65406832229f67eabbd9fbbf5661133c11c52008f92263c71b0; original global index 4741.
def localCycle00081 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -2, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 30 2, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 3e2ddbbecf9d45ec2e0f0fa268a2e529efb1a08b05c1b3e7d99fa24f5a8e20bb; original global index 4811.
def localCycle00082 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 3f767a33dc680e43fd35e8f99f42ab114440d780ff0d5fc04b4a179222ec9363; original global index 4903.
def localCycle00083 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .gapLower 6 4, .triangle 4 2, .triangle 14 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 4007896e30b41ad49a517bb29a7fa85a377aea067678275aded96f686d5f9d62; original global index 4938.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 40ac7453c8a465d646d441af02b925c6e570d4e91e0d5a8e77fcdc4d09083fe8; original global index 4997.
def localCycle00085 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 6 5, .triangle 18 0]

-- Original cycle 413bf921262ccc19563feb2790b0de92334327237a75d15f6d8c5d7a9367fdb4; original global index 5034.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 5, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 413f2faf368ed42a305aed76200cb02170e78e15bcb4859ff3889fe89e980eef; original global index 5035.
def localCycle00087 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 3 6, .distance 1 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 21 2, .gapLower 6 4, .gapUpper 3 2]

-- Original cycle 429190913187aba8b2f516215e17c3a74017936accca3ad90bf55d7f8d9a6446; original global index 5128.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 42f327725fabdeef6f429d24135125ad5ddcacb8d66cb398c5117d86461ef691; original global index 5158.
def localCycle00089 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 2, .triangle 24 0, .triangle 30 2, .triangle 8 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 438f8db23e701f5e80df116b27be954f0a1826da39b715bd595b12082398c8b1; original global index 5224.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 4452ac49d5e35a27ce13c265d1644ad6c77909250b63211128804b4006f2b6ee; original global index 5289.
def localCycle00091 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 11 2, .gapLower 6 2, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaLower 3]

-- Original cycle 457a1bf0ad55b68835be31a23742813eb66b0db4e6d633c9fcb04513632094b4; original global index 5374.
def localCycle00092 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 460fd9d1d731eab3a74dd77dfe4211a1637aa8ba6ab8609bba8f001bcfa02b8f; original global index 5421.
def localCycle00093 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 4675e109cc91fe5a5bd9ca12f9fcfa230997589103db2c5837a2247b1d1d0435; original global index 5450.
def localCycle00094 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 46c0427a1c2c8cb82e7947c9186fe27960323fb190d5d8a1ac4498792f1b6e8d; original global index 5482.
def localCycle00095 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 48978f05ae116806e6d4ad4336addf6d7a3ac10b957725b1aa156246b2a2dfc2; original global index 5624.
def localCycle00096 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 0, .triangle 21 0, .triangle 32 1, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 4949ac11fc9c70a71713b2fcda8c8452fe03fd6d747f2d8f398298638180ac2f; original global index 5675.
def localCycle00097 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 1 5]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 24 1]

-- Original cycle 4974f9986217de0466465703ac3b95532588be56a723f3e9266bc4e6cf2ea5cc; original global index 5692.
def localCycle00098 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle 4983d6ae972466a26624b807f164d71a2732bcf27aa922ec67deb579ea4a4815; original global index 5700.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 8 2, .gapLower 6 2, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 4a19b2693946d9e675bab4d98c2691cd5d14330a4eb4a1378c79972747522d1c; original global index 5752.
def localCycle00100 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 5, .triangle 21 1, .gapLower 6 3, .triangle 13 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 4a6a0807cabf381a71ec2c0bf16f986d0e4a119f11f756e96562e8d6c5940f50; original global index 5770.
def localCycle00101 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 4 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -3, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 29 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle 4b69d88e8829dd97da6f5c00f280c2b0f48019b26773aac7a80ada8a5cf218bc; original global index 5843.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 4cf0c6b28d77e248570e2372f100bd8098d8fb4d3d8154cc9d23c89137d48aa9; original global index 5975.
def localCycle00103 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 4e44b38a3c2fc3523b3b8209cf6e5443659db697d337795d7216ae5f28ff56fa; original global index 6076.
def localCycle00104 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 0, .triangle 21 0, .gapLower 6 3, .triangle 13 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 4f353fce6a6baa26ed34de71fe9f2b48dd3a57ec93b36869e6a8c960e3a0ecef; original global index 6158.
def localCycle00105 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 4, .distance 2 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5, .zero]
    constant := ![0, 3, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 0, .triangle 29 2, .triangle 8 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaLower 5]

-- Original cycle 4fb6edf5c20d2771e5c0fe364d38c83cce9d0976bdae39be84d58a6110455a75; original global index 6190.
def localCycle00106 : Cycle where
  length := 3
  data := {
    node := ![.theta 5, .distance 5 6, .theta 6, .theta 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 0, .gapLower 6 0, .thetaNext 5]

-- Original cycle 4feec6c59ea7f27acc557f5cd64f64690fb97c70bea1ea848de31dac43448717; original global index 6205.
def localCycle00107 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 0, .triangle 27 2, .gapLower 6 5, .triangle 4 2, .triangle 13 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 52836fc89deece694ece217733bdee36fc269d77b767ba206b959e49b3929682; original global index 6414.
def localCycle00108 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle 5454131691703683f7e0ecb391b054b9244ee34dd072a2c7b53352f829276c95; original global index 6531.
def localCycle00109 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .corridorLower 3 5]

-- Original cycle 54de1a3376ec605ddfc9b67a11e49dae395ad7b15c047cfc3931ce36586e775e; original global index 6571.
def localCycle00110 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 2 6, .distance 2 3, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, 0, 0, -3, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 6 3, .triangle 27 1, .triangle 26 0, .corridorLower 3 5, .thetaNext 2]

-- Original cycle 56d2975bbc49d04e5a6ed7792e73b37248c9582db500d37c6f6cbe0a46d724e4; original global index 6730.
def localCycle00111 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 29 1, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5803fddb96c9488f1086710f35e6cb16ea36953c0666ce5526c6cf9aa8152623; original global index 6830.
def localCycle00112 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 6 4, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 581a80d99d839b9f66ff25d08e531a60be0668f5fd5819aadb0b6431c8212494; original global index 6836.
def localCycle00113 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 5832b6138b8af592ba0c4e9d28d1f41f6bf25c2c5b42cd4f84b2cf7daef36453; original global index 6843.
def localCycle00114 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![2, 0, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true] }
  origin := ![.gapUpper 1 1, .triangle 24 1, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 10 0, .triangle 1 1]

-- Original cycle 58902c02faf498454b41fec2470e5a817035ca03334e3e03062c8de4fb69ec79; original global index 6874.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .triangle 14 1, .triangle 34 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 592c979471e620bbcc5f695e3f0e20e413ab0beaf84c932976450b7ca132ace0; original global index 6916.
def localCycle00116 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Original cycle 595c0e3200dc990b4efc6c1dc0336c372dab92bfe76911a00148c99f43042323; original global index 6941.
def localCycle00117 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 21 2, .gapLower 6 4, .triangle 30 0, .triangle 26 1, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 5b6a86c6d26b4ceec960c08bf8d94104c99760326a9cda9cf53ebe47cc5de7e2; original global index 7113.
def localCycle00118 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 2, .triangle 12 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 5beb66ddfc02fb6625064d6e9805cbeb7f4aa201445d7299e791e4612575bebb; original global index 7148.
def localCycle00119 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 5c0a2313e07bd45c9a1ec1ea37a0af96d8eafd93fb46e5f913f0de76dfde7a4b; original global index 7162.
def localCycle00120 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 5cbdbbbb9ec423f07b1f2a45ded82c0398c5052c1abfa95a2ac97d461395ab15; original global index 7217.
def localCycle00121 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 11 2, .triangle 13 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5db2508198d178b9e3add2fbc9b352a90d5d46d17fe4fc6d2e9b8facdd5686f7; original global index 7291.
def localCycle00122 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 0, .triangle 18 0, .gapLower 6 3, .triangle 13 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5e9db983543d706b4007e2e34e09890e9c04ad58450b4cc5e911ae1700c2bcef; original global index 7358.
def localCycle00123 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 5, .gapLower 6 4, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 60f05ee3b7061fc2b9a780203518b388487ca551e5f6f0a6b1ec96ae8791c2d2; original global index 7554.
def localCycle00124 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .gapLower 6 3, .triangle 13 1, .corridorLower 4 6]

-- Original cycle 60ffafbb890a439796625112ee96a87554eaa9a34549338c8dfcf4dde2aa6232; original global index 7560.
def localCycle00125 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 32 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 657d31b2f036402b03c6a069be44519284ac554d8c7dcf1f95bbe3fe16b22a6f; original global index 7897.
def localCycle00126 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 2 6, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 18 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 667d5313ea3adfa43ff9941b980cd6e9f116ecf727e9f8388b696f870a52a51e; original global index 7968.
def localCycle00127 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 66ff1897ddfeae1761ee5b7cf5f420775541a4fb44c7c987bd122aa05743c888; original global index 8001.
def localCycle00128 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 673d02c0a2e7c4cbe8d70e958a57294da3a17d476e3a7bbb33e50a536978024b; original global index 8024.
def localCycle00129 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 6759d2307de4ea5cb144ab7cd3c25b3ff471c7a5d961f9c7ee63685d8dd03e6c; original global index 8034.
def localCycle00130 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 692617ac15a1e9788fccee33eb2ab6b0ace157fc2fa9bdc4e22b82fd882c80e0; original global index 8177.
def localCycle00131 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 695a0e8bc662c99a43ae8ef34ebd2089872a9df858d5d2e095dcc0522906f3c8; original global index 8197.
def localCycle00132 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 33 1, .corridorLower 3 5]

-- Original cycle 6a32ca19e70c6ff046e5344912c37aef7f59ce64e8f7899d8e4f559a2b441a65; original global index 8265.
def localCycle00133 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 8 2, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 6ade187232a4e09d09432243bd3934d5ee2a9c605e7996bbf1faef37cdd20f82; original global index 8321.
def localCycle00134 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .gapLower 4 0, .thetaNext 3]

-- Original cycle 6c52e8b35653e2608f7c5a7067ea69774d1f2198d445956673f994666b89604c; original global index 8439.
def localCycle00135 : Cycle where
  length := 5
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle 6e700030893f7c6db3d7397b3be4bec96185911c0143a992c9b83f3b7748b201; original global index 8570.
def localCycle00136 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 1 6, .distance 1 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .triangle 21 1]

-- Original cycle 6f07abf71490ebd876dd0219841890d8a98fc9302991703ec07f6080e8c26a22; original global index 8611.
def localCycle00137 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 6f39f216909ba0c0d92097177cd7db1658d35df76afb3b6832e97215ab5e9370; original global index 8622.
def localCycle00138 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 2 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -2, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 29 2, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 7184847694214a045982e0a34ae81e302b62707976af776f036e7d5f7aa48c34; original global index 8810.
def localCycle00139 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 72142a219ff5a856221ee55deb8b69df9ed2f0a85d0c74f7b99b7d198fb44038; original global index 8841.
def localCycle00140 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 72fe0da38127ef77fb0f5747991fb12f87890beaac7a4176ebf096cc2a15ebd9; original global index 8909.
def localCycle00141 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 3, .gapLower 6 2, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 73510f3f7151d630fe3f1b4e1e3334d20a7accb694658a8f09be7cd4ce7b3ae8; original global index 8926.
def localCycle00142 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 737b90c6ce7f98ba69eee4f29198819a7d3925a328af29f9332cebd51b71d87f; original global index 8952.
def localCycle00143 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -3, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .triangle 14 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 7392e48ac379b717e22a0a4c14245ffc9a0da2fb0be67cb23ddb88ca0a48293f; original global index 8961.
def localCycle00144 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 73cff67f1ce2fc038d6b71d9563e9fdf157862a7661d6d84510bc88827c7e293; original global index 8979.
def localCycle00145 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 2 6, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 3, .gapLower 6 3, .triangle 30 1]

-- Original cycle 766c7209ccf6a1ce40d75ccb567ebb1bcf6e04c29c44303f7114d1581fdc3c05; original global index 9168.
def localCycle00146 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 4, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 0, .triangle 25 1, .triangle 27 2, .gapLower 6 3, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 76c20cacb30145dc8c9658833df341d0e67c04c82e23392e31664853025e0688; original global index 9190.
def localCycle00147 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 76e2295c8df61bddf1e155197a9d9518dd33cbac022afc43e508443796bb2bf1; original global index 9201.
def localCycle00148 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 5 6, .theta 6, .theta 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -2, 0, 3, 0, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 12 0, .triangle 34 0, .gapLower 6 0, .thetaNext 5, .corridorUpper 3 5, .triangle 33 2, .gapLower 6 5, .triangle 18 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 79530a3a98d000e0023f1bf4ed550e91cf41cb1a5ec698b4be3c1eb23ddb99e9; original global index 9388.
def localCycle00149 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 79d8a3ed6ce99298ed9a6bf104b773d70da685bb961d072595583af416fec771; original global index 9424.
def localCycle00150 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 29 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 7c201a7e87a92da3584078ea1cacc7660ee0371f4b8cf000ec37f0667fbb5be5; original global index 9603.
def localCycle00151 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 7d78f391f79b6ad01442b844b3f2feb782d02b25da15dfd8a0b003f611d3e993; original global index 9732.
def localCycle00152 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 6, .distance 1 3]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .triangle 21 1]

-- Original cycle 7ddd83272ce547a411c9669fc5fbe955b70ef93a241f45c22867e7b6de5339f4; original global index 9775.
def localCycle00153 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 3 2, .triangle 14 0, .triangle 34 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 7ec29b9ab698c01a5083363025387ae1b9233dd834534450c0400466a1f681d6; original global index 9845.
def localCycle00154 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 807f58b206ce8ec43f85b81ef7c34eeb97d75f41c0b0fbfa03ef3926dc837d35; original global index 9973.
def localCycle00155 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 0, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 80cb32c2adfa2f9cdab4ec7717dd46bd2059122c0227562fd26f6b8f0bd613bf; original global index 9998.
def localCycle00156 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .gapLower 6 3, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 81424769202e209a3ba16a308617dbf3fceae0481ff49f4071f02801b3b552f5; original global index 10033.
def localCycle00157 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 26 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 84461a5f6ffdefc34313f300757cc5586698c975e26464456bb2a6409681013d; original global index 10272.
def localCycle00158 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Original cycle 84b7b93784d59b9d6b99f7ce4a85ebd9cd486a174e2a5044bc3b6a70cdb370f9; original global index 10302.
def localCycle00159 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .triangle 13 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 8507afc2710ccd4056452517605c97a43ad444497c9329379cad24e08b64a7b6; original global index 10325.
def localCycle00160 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .gapLower 6 1, .corridorLower 4 6, .thetaLower 4]

-- Original cycle 8543e92669673ecbcb9f309411486d1623a9beffea07967b51ad908ccc9cd769; original global index 10338.
def localCycle00161 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 8604cf705b5f34a506fe383518c4414a160d1fe5427b48382bfd59266d48a708; original global index 10396.
def localCycle00162 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 8642f1ba0bb5d96f897c8d393b6da372437b0ac8f4bdf3b02d51ac6a0e88a952; original global index 10410.
def localCycle00163 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 892438758687eed8b3485b6f2c098406c2b52f0ec02a1055fe08546e8b6e1a04; original global index 10613.
def localCycle00164 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 1 6, .distance 1 2]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .triangle 18 1]

-- Original cycle 894b59c67fc28583c3cdfc836e8c3c6b031b3aee4c91253fc2dd431efca23f7d; original global index 10626.
def localCycle00165 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .gapLower 6 4, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 8a89a97a51beb062890cb94daa205184d1eb00dc59a0a10ec636bba31961b5c6; original global index 10731.
def localCycle00166 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 4, .gapUpper 5 4]

-- Original cycle 8b2b05719ebdcc8d2bd2a95d290369cfb0d424e629fad729d6e0c6f4cea1c3dd; original global index 10781.
def localCycle00167 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 1 6, .distance 1 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 21 1]

-- Original cycle 8b4ddd5fc7df912dbb933d496b4dc54bfd890d949dddd569d05cd4bfb7f5563d; original global index 10797.
def localCycle00168 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 6 4, .triangle 8 2, .triangle 13 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 8d7ab97e31a47b5da70ad49fdc083983700afe7dfb5da7c6c662d202b9cc70a7; original global index 10938.
def localCycle00169 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 1 6, .distance 2 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 27 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 8ec210d9460cf03edafed2190b02916c24b3eed999f9b4c06698229c7d884b8e; original global index 11048.
def localCycle00170 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 8f0fd28b18ba001419023d6c650ab653f5436eaec4aa3beeab07b49d1f10b57f; original global index 11069.
def localCycle00171 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .triangle 14 1, .triangle 34 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 8fa381035d650f5ff07c04c8a0bfcbd09eb33c72a4123bea3b34db514159183e; original global index 11117.
def localCycle00172 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 33 2, .corridorLower 3 6]

-- Original cycle 9126b6d7e2ccdb7f66223690845eab18748c4f42203cebd518fe4d23f33b85d4; original global index 11241.
def localCycle00173 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 0, .gapLower 1 3, .triangle 21 0, .triangle 27 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 912ec1826b43da3b2e046cd75961e684a49059ff034750f56aa123f5b37cedc2; original global index 11243.
def localCycle00174 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 2 6, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .gapLower 6 3, .triangle 30 1, .triangle 26 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 9304e1684235fd0231519f9ca955fb560308b3e38f909884a166402e1c7625f1; original global index 11400.
def localCycle00175 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 4 6, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -2, 2, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 29 0, .gapLower 6 0, .gapLower 6 6, .triangle 33 0, .triangle 20 0, .triangle 15 1, .corridorLower 2 3]

-- Original cycle 935eaeb414d65cfd77a988f439947ba6367e6a4768a9e25b7e26726211712e47; original global index 11429.
def localCycle00176 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 1 6, .distance 1 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 24 1]

-- Original cycle 93aa402e52381c5a9a6b7b10c4504815a064483e95563c121200b75b71da696d; original global index 11455.
def localCycle00177 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 1 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 23 2, .gapLower 6 3, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 93aae4dd5e297271314f283d634918de8b839c123dbf3797629d80c1dd7d0305; original global index 11456.
def localCycle00178 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .gapLower 6 4, .triangle 18 1, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 94551ace336cd300562e014f30087dae6f4f15436053cad18190cfc146a33b1e; original global index 11509.
def localCycle00179 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.gapUpper 1 1, .triangle 20 1, .triangle 26 0, .triangle 5 0, .triangle 0 1]

-- Original cycle 955cbef5557bca26737655ecbafe4d8ea44442ba40e9ab115d5dc8d915d378c4; original global index 11606.
def localCycle00180 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 30 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Original cycle 955f5876b48cf39dc8dcec3a6d57246df5864119c20da83d1b7543655de5f5bb; original global index 11609.
def localCycle00181 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .gapLower 6 3, .triangle 13 1, .gapLower 4 0]

-- Original cycle 95e1f7ef2aacd52ea3174e672489810289a0d1e2d26d1a37ec4e2c400ae1428f; original global index 11651.
def localCycle00182 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 5 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 24 1, .gapLower 6 3, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 971256ac27eb819a4932fb65d92f5e2946cf8db759899bc3fccabb6797056e25; original global index 11741.
def localCycle00183 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 8 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 97996238a5dcff1f1a654f573608ab2291fe10122ecbddd7ddccc62cb02f4d67; original global index 11775.
def localCycle00184 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 97bfd9956f954103268f4fcbdd8a559d10cfa36a4e19e4f3902587bbc1ef7e60; original global index 11785.
def localCycle00185 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 30 2, .triangle 8 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Original cycle 97ece87445c15ead48a72a9cc43ea966be2bb91555ab6e31c9a1560ab6844b97; original global index 11798.
def localCycle00186 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 99b7fac89cbb94fcae131e85b417565c2829209d2793169e9bf71c8a525d591d; original global index 11934.
def localCycle00187 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 3 2, .triangle 14 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 9a53bb4a0784947dc3649e163a0909b37eb043fafdd96d5958278b7730a6647a; original global index 11993.
def localCycle00188 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 4, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 9a92d45e7b6348eb83bebb53e1db07dc64a695ae1a190ea229fbb474de2e56ea; original global index 12007.
def localCycle00189 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 0, .triangle 30 2, .gapLower 6 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 9be251bebf69eab9005c7632e0f84b6d2302b928e69f29c555556d526f4ecb56; original global index 12125.
def localCycle00190 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Original cycle 9bff84545b48bd6552206bd50d43b318fc368dcf1ad332b02f27d838d4f09b05; original global index 12134.
def localCycle00191 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 3 2, .triangle 14 2, .gapLower 6 2, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 9c9be1636719e494dadf4526e3fc09cff8eb85070e375acfdd5ed5a39b2d4a03; original global index 12183.
def localCycle00192 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 27 0, .corridorLower 3 6]

-- Original cycle 9cca7e67c401e1c6d3eecaebed138ec3ce7f7418a993c3c485cf8644f7650586; original global index 12195.
def localCycle00193 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 6 4, .triangle 11 2, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 9d43067b6667c4607d89fe13c7fb194019e3177662a24c9a0683f1fa86718ec0; original global index 12234.
def localCycle00194 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 9dca8990d32eb12411de2a03001dc83b935e24559d30281f2a28ccd1aba041e3; original global index 12275.
def localCycle00195 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 24 1, .triangle 30 0, .gapLower 2 2, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 9f2f3239e3b5dc6618f6c97ac50908ded27e762786e6ea85b75c4e93f892bd4e; original global index 12393.
def localCycle00196 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle a57af7a60f30968dcf15141346c3d7217f43c03319008a42f722ce755724adae; original global index 12859.
def localCycle00197 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 2, .gapLower 6 5, .triangle 8 2, .triangle 14 1, .triangle 34 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle a5bb7b5c7d4e2e4760a681d086ccd59e48d7afa41554849c880288a70ead337d; original global index 12875.
def localCycle00198 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 20 1, .triangle 21 0, .triangle 27 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle a70b1d8bfc2c67d65cbc3366aac4f4b3f9d7237051b0e4ab9206fe71ba593481; original global index 12983.
def localCycle00199 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle a9707215f99a8e69d5fcd6ef958d61def534f35a301e1e20c240afc21aadd29c; original global index 13190.
def localCycle00200 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 3 6, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 33 1]

-- Original cycle aa6e1216530d7100e46f7bf41ff7e7660c611424555b3cc79265d7aa1809d98e; original global index 13275.
def localCycle00201 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 18 2, .gapLower 6 3, .triangle 14 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle aa8e1ab38e50b93fd8a7257890539a81e589eba6d4bde628e7aeed9317e47181; original global index 13284.
def localCycle00202 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle ac1e086435000171b7f3f683ae87ec28e7fcb67d65ba86595a8b2fc3677cb413; original global index 13411.
def localCycle00203 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 6 4, .triangle 8 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle ac2117a38cd216b2f4fb1c30f08f063ce53bbb0326b5c215d6af9e7013d0b7ee; original global index 13414.
def localCycle00204 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle ad952dc17c5eb8968ceecf0fee780984e8a9e45679937dd9ccbc4d30c76cec83; original global index 13548.
def localCycle00205 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 2, .triangle 24 0, .triangle 30 2, .gapLower 6 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle af80b9228b17629cab283e0a4c1c8195569772000a2034e95203dd226ffd6e52; original global index 13705.
def localCycle00206 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle b07ea2d825f69ca1c4b106d78cc84c4d1a2447c2bc3ef75806ff3deff6da98a6; original global index 13781.
def localCycle00207 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle b0a65d5ec74dc3d83775ae3456745dfc09969d4a1dace3929e4ec8d8240e7787; original global index 13793.
def localCycle00208 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 20 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle b30b61fa1251965ecd84ddf4d63bf23a703170db0e2d7b106471c640ccc06ab6; original global index 13991.
def localCycle00209 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 3, .triangle 13 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle b4efd9996270dd78fcf9b5596b2e2da14c1c715c807116f4c4854c5b5e73154d; original global index 14132.
def localCycle00210 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 2, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle b5a3bde6bfb039d82b486de24bb465133087136b2080c8a5cae0e2779a99e8c1; original global index 14192.
def localCycle00211 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 6 4, .triangle 11 2, .triangle 13 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle b836607d17b16c57e6ecc39c693a6495d8c8f5dba302a90448b08a9e9fcffa1e; original global index 14371.
def localCycle00212 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle b94fb0559ebd2dd2857f868638b86bd1bf48d906321ab055725a6c34ef98c9eb; original global index 14459.
def localCycle00213 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 2 6, .distance 1 2]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 18 2, .gapLower 6 4, .gapUpper 2 3]

-- Original cycle bb110969772848596f716a446c1a137d7da94abeb946db61f8bfb30872948dcb; original global index 14609.
def localCycle00214 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 0, .gapLower 6 4, .triangle 4 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle bbbb5e6e397aeb2358d49010b6d1f325f2875a8f09e864fea643baaaa6acd8b6; original global index 14660.
def localCycle00215 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle bc7cc33b269408f91651dc02771f7b846f2c5cd6d4fcf8619ad0848633551de6; original global index 14708.
def localCycle00216 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 2 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 18 1, .gapLower 6 3, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle bcb8dc8a509bc963d132bf5bd61497037ddd51a77a4b230a68c55d6352251d18; original global index 14720.
def localCycle00217 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 0, .triangle 21 0, .triangle 11 2, .gapLower 6 2, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle bfb2c5e4ebdb703ae12b3298e5fc0de198de41a38296bafefea0a88d3f96d072; original global index 14953.
def localCycle00218 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle c17b3d02820486609342093478ea1920886aebe922af4d28b7e897db49a9c3e2; original global index 15110.
def localCycle00219 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .triangle 18 1, .gapLower 6 3, .triangle 11 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle c374f607e6edec3b6dea5850b823bde6d69ec72ce0c52b99f3d739555e8fa409; original global index 15253.
def localCycle00220 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 21 2, .gapLower 6 3, .triangle 14 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaLower 3]

-- Original cycle c74f2fcfb03b9d65ec81e5bf85d314669e9a7629cc9d5c4909a6e07a17ea5fe9; original global index 15552.
def localCycle00221 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle c7ee013a7502bf2f19cf7c639e12dd86bf97d394e8025f018c70cd231d379c1d; original global index 15608.
def localCycle00222 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 24 0, .gapLower 1 2]

-- Original cycle c7f6cd77f99a650c81f724391110a574c5b12d1ecd0207a080a511eaad87e0d2; original global index 15612.
def localCycle00223 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .gapLower 6 3, .corridorLower 2 6]

-- Original cycle c923ac73aa78db1e92197ce53d0d8e4c0b0a94a449cbe8259bf5207f0656d5de; original global index 15714.
def localCycle00224 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .gapLower 6 4, .gapLower 6 3, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle ca72b9881fed6cabf7991c6af2b563ab47ecdd895665e4382c917181d7523d09; original global index 15824.
def localCycle00225 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, 0, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 21 2, .triangle 24 1, .triangle 30 0, .gapLower 2 2, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle cb01fd46c945f7f6b311b99522091881fc4e272c6cc6580b782e0bc46cb5592b; original global index 15861.
def localCycle00226 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .gapLower 6 4, .triangle 34 0, .corridorLower 4 5]

-- Original cycle cba200e9510039c2f43ca8f8dee8dc4881c5d663a86103d9f4a7ecde8a5be489; original global index 15911.
def localCycle00227 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![2, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.gapUpper 1 1, .triangle 24 1, .triangle 33 0, .triangle 26 0, .triangle 5 0, .triangle 0 1]

-- Original cycle cd70ee819e4080f1871eac0843ca3d8c551c9331a6614956b0c14a2444ee1195; original global index 16058.
def localCycle00228 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -2, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 6 3, .triangle 8 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Original cycle ce7eb74e34012ee5e61181acf2da51020e69f642e1ada7ac676a01e015b0db85; original global index 16126.
def localCycle00229 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 4, .distance 4 6, .theta 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, 2, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 0, .triangle 29 0, .gapLower 6 0, .gapLower 6 6, .triangle 33 2, .triangle 21 0, .triangle 15 1, .triangle 26 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle cf147975a2ee2514939f4b783987faaec8cb1e678a0190f18d0c25d7f270a875; original global index 16158.
def localCycle00230 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 2, .gapLower 6 5, .triangle 4 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle cf261df64878600732d54fb8b87697f05b7bbe9df0f54140f15a8fde9c78cccd; original global index 16164.
def localCycle00231 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .gapLower 6 3, .triangle 14 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle cf9a36e4772c4074e805ae070dcc52317a3cdf1caaa32c64ed92caed9565a142; original global index 16199.
def localCycle00232 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 32 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d01f5a019e0223d5978e3d85dc79a4765a7190b336d7b7c069dd8545b9aab777; original global index 16248.
def localCycle00233 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d166417f866829f5f6a335eadb3b5e3de99ea521934b9e47320d1b69fe32d20e; original global index 16345.
def localCycle00234 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle d1a6213108fe88114107dea4a35a638617314f6c26c785fcfdc67d3cbd593ae3; original global index 16362.
def localCycle00235 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 21 2, .gapLower 6 3, .triangle 8 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle d2510646bcd7d242b03c593a0f2999abcd4311896578eeb84fae3ce407ff7bc1; original global index 16407.
def localCycle00236 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle d26dfdd1db50de8c91698eab4dcccd1c362dc9d0a9956edf8e9e9bbcd68c91e6; original global index 16419.
def localCycle00237 : Cycle where
  length := 4
  data := {
    node := ![.theta 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 0, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d29fd8a486b265e0bbf361844f10639e0075c2002bc96a73cedf3768b316881b; original global index 16436.
def localCycle00238 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 2, .triangle 34 0, .corridorLower 4 5]

-- Original cycle d2ec4fe647c742d857ae6e0ba6eb19dd305a12131e87489b7b4b6d2ab1e6a17e; original global index 16454.
def localCycle00239 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 2, .gapLower 6 3, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle d3202f4ab0d00437925e3aa5226bc6195192d245fbe2e52e11925605f1d5406c; original global index 16467.
def localCycle00240 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .gapLower 6 4, .triangle 4 2, .triangle 14 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaLower 3]

-- Original cycle d3ca438ad907f6358603c5bab95f53595d20511a13a1d2901f433a26fa40939a; original global index 16527.
def localCycle00241 : Cycle where
  length := 4
  data := {
    node := ![.theta 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 0, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d5a60eb5428f2d36ae0321ea81937aa3df80321d72b85e9fee14212d06a908a5; original global index 16678.
def localCycle00242 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 6 4, .triangle 8 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle d5e557fe7f98c7a98021040116560c1816e11dc1b71966018a552e177a83c25d; original global index 16693.
def localCycle00243 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 4, .triangle 8 2, .triangle 13 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d72545ed74e0c078dc7d650e416ec65f1d374f226061c2749f457ae02a6cb0da; original global index 16791.
def localCycle00244 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .triangle 34 0, .corridorLower 4 5]

-- Original cycle d7f9b2e4ede53dfefcb3e811fac88473c55c771005580ed9ca71977a22f9a81b; original global index 16854.
def localCycle00245 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle d8ac257bf232308a6cdd26a90a8356b8b2508684f7bf0d482e73b73abd1ce779; original global index 16914.
def localCycle00246 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle d9b87e0de290f3c29a84e23212c76e14860381c25bcf7c79d17df66cc1e38f49; original global index 17007.
def localCycle00247 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle da729aecafc838fddbd0c47b422940d9a975dd79e3de0a99ef756223befa7ab9; original global index 17073.
def localCycle00248 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle daa48aea80c2800e75f83986a8325a376596711e404be7c9519eb344e271f541; original global index 17086.
def localCycle00249 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 2 6, .distance 3 6, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 6 4, .gapLower 6 3, .triangle 11 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle dab3bd1984676b366160e2d060d27d4c5998b4aa2a376ecdd1b3f6421449504c; original global index 17091.
def localCycle00250 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 1 6, .distance 2 6, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 30 1, .triangle 26 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle daf618e7090458a96c1d4b6b1a600a0be39fb50f5bfee59cb5cd61dcfce9920c; original global index 17108.
def localCycle00251 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle db3f0804d156b4f76ad83c9b1f328a8b49a4483009544675d636369364bebf9c; original global index 17137.
def localCycle00252 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 0 6, .distance 5 6, .distance 4 6, .distance 0 4]
    constant := ![0, 0, -2, -2, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.triangle 12 2, .triangle 14 2, .gapLower 6 2, .gapLower 6 1, .gapUpper 4 2]

-- Original cycle dc23debd045cfe545dad55bd62c666f196530ba95534e00fc9c0eeaceb4a4ba9; original global index 17204.
def localCycle00253 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 4, .gapLower 6 3, .triangle 13 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle dc257873c2af2cf0e2882ab9796433415793a720b993385c9e883b49512c3b5d; original global index 17205.
def localCycle00254 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle dcd78e05abdd4660577b698211756ed75c32dfb01b554352297989aac2ff1aaa; original global index 17259.
def localCycle00255 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle dd13157ad160025f23fa9d46c550a25efcbcfe96cb3ceee36fdcff41c85e0392; original global index 17282.
def localCycle00256 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle de5f761374a630e8403a02c90d440fd601768e629a2545dbfa0af8ee353a45a8; original global index 17384.
def localCycle00257 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 24 0, .gapLower 1 2]

-- Original cycle de6ccc16e1d84b7e4a3f1f8e76bc02388f6211fa0e0808a8ce5ce0466453de95; original global index 17386.
def localCycle00258 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 8 2, .triangle 13 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle de944b0f04946a6513a76cf65c1c8a8ca4059bfa52a4eb670f48b23677f84391; original global index 17404.
def localCycle00259 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .triangle 30 2, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle e0247aa42d2abc65d22cdbfe0f8c232971b6797cb3282d5b42ea438737d3c642; original global index 17521.
def localCycle00260 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle e04304cb32a70cf8147445725b0500c41b2bbbd6c1727ae96c71e4455e8a8344; original global index 17531.
def localCycle00261 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 21 0, .triangle 15 1, .triangle 26 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle e29c6e5bf2a6e058ce34e746548105c71d9890051eebf22cc2468350fafa31f3; original global index 17721.
def localCycle00262 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 26 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle e2e3d1ee6a03ddca4383b98e16e71f7af0b36fd200d2e27b0bfb0007b4bc081c; original global index 17748.
def localCycle00263 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 2, .triangle 24 0, .gapLower 6 3, .triangle 8 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle e317dec798ba1162ca84bc8085c7a46987f7950e79026ba8319210c85791819f; original global index 17757.
def localCycle00264 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle e364b9883d887a508bcd08e81c7d82c29f58ea339c678d8a4739008e1df626df; original global index 17782.
def localCycle00265 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle e3bb372fcaef8247878717490c8f26bc94ed1f985ca2a550f0d269b1906481de; original global index 17808.
def localCycle00266 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 1 6, .distance 1 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 4, .gapLower 6 4, .triangle 24 1]

-- Original cycle e4166c04e5da046071c91b989fb467930f613be595c6d6be4fe427069d9021e7; original global index 17839.
def localCycle00267 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 0 2, .theta 2]
    constant := ![3, 0, 0, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 30 2, .gapLower 6 2, .triangle 8 1, .gapLower 2 0]

-- Original cycle e554c934539ad50aafaa8a5b435b3b538938f0e4f8da244f413ded3917874832; original global index 17930.
def localCycle00268 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, -1, 0, 0]
    strict := ![false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 2, .gapUpper 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle e69e961dee22a36b4265d58485a5ed5447ac83a4e90a926265e8bf1f6346e267; original global index 18038.
def localCycle00269 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 8 2, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle e6dbb5fb8bd0463af1c40b8e5d350e6a87c573e381492141cb6262ebf54195b8; original global index 18063.
def localCycle00270 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 4 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![2, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.gapUpper 4 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle e949063d2b5e58409fcfbdb94be39952e4de964af110fa52d72302b234d1d3a9; original global index 18228.
def localCycle00271 : Cycle where
  length := 5
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 6 3, .corridorLower 2 6]

-- Original cycle e97bf6f13ef56efe1623f3f093088b705fcd02c541cd78183a3d2325186670c3; original global index 18246.
def localCycle00272 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 2, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle eac41b30b93f0de3d49c20c55ee80768a38c075446310a390e54cb4824141e1d; original global index 18336.
def localCycle00273 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 2 5, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 28 2, .triangle 7 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle eacdf5c8107af19a613ba66606dbac9deea95bd11933240f9993e315373e51c2; original global index 18340.
def localCycle00274 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 2, .triangle 2 2, .triangle 12 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle ebe0273ec4d2c4d8f8ec2250bf322b86d6ffc922dced31012e683c243c1ba567; original global index 18409.
def localCycle00275 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 6, .distance 2 6, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 2, .gapLower 6 3, .triangle 30 1, .triangle 26 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle ec43b3176e4a48b103f6a9aad54143aa4f355d9e922f9cf93709bfd95b8942c9; original global index 18442.
def localCycle00276 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 3, .triangle 11 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle ecbd8f89ba058a8c81a68d45e7c129dbf604a048e0c5278cc2e000bef72c1737; original global index 18481.
def localCycle00277 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 6 4, .triangle 27 1, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle ecf6ddb9936bc7d7d7078b04e87c6983a221aeb60d667fc9ea9b1a472a8c22e9; original global index 18497.
def localCycle00278 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 14 2, .gapLower 6 2, .gapUpper 5 2]

-- Original cycle ed3e0f47c3a160b356a4a6fdffc97d6ba40d16bcae46a7a88f942b69e0bbb585; original global index 18524.
def localCycle00279 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 29 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle edd96e5b0794afdf5ee98c3a0c7e6f4ab81e9cec26bb0749dec3522221f2929b; original global index 18570.
def localCycle00280 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle ee8dc13a3e98c76c09e03206aeea44c959cbe56e58b68b59c8f2aee260109a94; original global index 18615.
def localCycle00281 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 12 2, .triangle 14 2, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle ee9cfed25cd31422b638e569729dfaeb81d4df1c220328d54dc56b7dcfe621f1; original global index 18621.
def localCycle00282 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 28 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle f0a0e20e56c555877a21e099b765660d716bc3fc6d7ea271c16cb7356f59ea6b; original global index 18765.
def localCycle00283 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle f113fa158cf54ff589f0d4c5a992fd0c385871c104b7690a2277cd884b49edf1; original global index 18805.
def localCycle00284 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle f19d74d57c656d553fdc5dcfff3102b887f051e7f3538ba303f902a67eac1210; original global index 18839.
def localCycle00285 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 26 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle f35cf1960ab58268dd889697c128b28346cee46521116d303fdc5d92c92a1d17; original global index 18982.
def localCycle00286 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 2, .triangle 24 0, .gapLower 6 3, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle f44015bdcb74534b1faf890ccf31a8443e214248e9ac717de922e8dcb785f45d; original global index 19045.
def localCycle00287 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 5 6, .distance 1 5, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, 0, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 1, .triangle 24 0, .triangle 17 1, .triangle 26 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle f4edd0bd37154fd2fe0a0a61665d393e8874d650c5501b4c9c98fcab63e433f1; original global index 19099.
def localCycle00288 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 8 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle f5c039cd10d931fe9e70aad3a793f64f9d43d79332e8edaf752a799b1f50a272; original global index 19172.
def localCycle00289 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .gapLower 6 3, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle f5e629243e486ccc4fe9a96d46c7eddcdfe10d01aec7cf4f9fc82822b6f11c93; original global index 19187.
def localCycle00290 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle f8cfd4e8f5ba2d13ac0c5aabbce3dd1403496ce965c11aab9a1dd95479e1fa6f; original global index 19407.
def localCycle00291 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle f8ff6805347261315bd8fe541be955420b9eb8443e00a338c88b72f2ea9aaa8a; original global index 19419.
def localCycle00292 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 1 6, .distance 1 2]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .triangle 18 1]

-- Original cycle fa9bcc513d7961a0b81af8ccc16ebfd1f7dcbe0d9b784c91d186de32a8bab3f5; original global index 19552.
def localCycle00293 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle fc2002a8e79135f2cf3bbe1b8095adc484bb97f3843ccc473b6f10d0ae266589; original global index 19687.
def localCycle00294 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle fd404bebfa65f8cb6b2eb64e9a649e66c8fa6c3fa5e2cf1c748f889a3e4c0260; original global index 19792.
def localCycle00295 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle fd5719ee765f5843301266b1928e2ca9ad93e35c47be1bdd42b28c2e0278029c; original global index 19799.
def localCycle00296 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 5 6, .theta 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -2, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 12 0, .triangle 34 0, .gapLower 6 0, .gapLower 6 6, .triangle 27 0, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle fef47a891689ad5c12d346067a8dc5e9abb7aa82456abc734a28e0435dce06fe; original global index 19934.
def localCycle00297 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle ff86537f79915d3dc646946da9bc301233c4c48e8dc142a47557cd3fabf12194; original global index 19979.
def localCycle00298 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 1 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 18 1, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

def library : Library := fun id => if id < 149 then (if id < 74 then (if id < 37 then (if id < 18 then (if id < 9 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))))) else (if id < 13 then (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none))) else (if id < 15 then (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))))) else (if id < 27 then (if id < 22 then (if id < 20 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none))) else (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none))))) else (if id < 32 then (if id < 29 then (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none)) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)))) else (if id < 34 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))))))) else (if id < 55 then (if id < 46 then (if id < 41 then (if id < 39 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))) else (if id < 43 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))))) else (if id < 50 then (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none))) else (if id < 52 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)))))) else (if id < 64 then (if id < 59 then (if id < 57 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none))) else (if id < 61 then (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none)) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))))) else (if id < 69 then (if id < 66 then (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)))) else (if id < 71 then (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)))))))) else (if id < 111 then (if id < 92 then (if id < 83 then (if id < 78 then (if id < 76 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))) else (if id < 80 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none))))) else (if id < 87 then (if id < 85 then (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none)) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none))) else (if id < 89 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)))))) else (if id < 101 then (if id < 96 then (if id < 94 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none))) else (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))))) else (if id < 106 then (if id < 103 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)))) else (if id < 108 then (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none)) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none))))))) else (if id < 130 then (if id < 120 then (if id < 115 then (if id < 113 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none)) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none))) else (if id < 117 then (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none))))) else (if id < 125 then (if id < 122 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)))) else (if id < 127 then (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none)) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none)))))) else (if id < 139 then (if id < 134 then (if id < 132 then (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none)) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none))) else (if id < 136 then (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none)) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none))))) else (if id < 144 then (if id < 141 then (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none)) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none)))) else (if id < 146 then (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none)) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none))))))))) else (if id < 224 then (if id < 186 then (if id < 167 then (if id < 158 then (if id < 153 then (if id < 151 then (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none))) else (if id < 155 then (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none)) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none))))) else (if id < 162 then (if id < 160 then (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none)) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none))) else (if id < 164 then (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none)) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none)))))) else (if id < 176 then (if id < 171 then (if id < 169 then (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none)) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none))) else (if id < 173 then (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none)) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id = 175 then some localCycle00175 else none))))) else (if id < 181 then (if id < 178 then (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none)) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none)))) else (if id < 183 then (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none)) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id = 185 then some localCycle00185 else none))))))) else (if id < 205 then (if id < 195 then (if id < 190 then (if id < 188 then (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id = 187 then some localCycle00187 else none)) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none))) else (if id < 192 then (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id = 191 then some localCycle00191 else none)) else (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none))))) else (if id < 200 then (if id < 197 then (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none)) else (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none)))) else (if id < 202 then (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none)) else (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id = 204 then some localCycle00204 else none)))))) else (if id < 214 then (if id < 209 then (if id < 207 then (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id = 206 then some localCycle00206 else none)) else (if id < 208 then (if id = 207 then some localCycle00207 else none) else (if id = 208 then some localCycle00208 else none))) else (if id < 211 then (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id = 210 then some localCycle00210 else none)) else (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id = 213 then some localCycle00213 else none))))) else (if id < 219 then (if id < 216 then (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none)) else (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id = 218 then some localCycle00218 else none)))) else (if id < 221 then (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id = 220 then some localCycle00220 else none)) else (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id = 223 then some localCycle00223 else none)))))))) else (if id < 261 then (if id < 242 then (if id < 233 then (if id < 228 then (if id < 226 then (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id = 225 then some localCycle00225 else none)) else (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id = 227 then some localCycle00227 else none))) else (if id < 230 then (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id = 229 then some localCycle00229 else none)) else (if id < 231 then (if id = 230 then some localCycle00230 else none) else (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id = 232 then some localCycle00232 else none))))) else (if id < 237 then (if id < 235 then (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id = 234 then some localCycle00234 else none)) else (if id < 236 then (if id = 235 then some localCycle00235 else none) else (if id = 236 then some localCycle00236 else none))) else (if id < 239 then (if id < 238 then (if id = 237 then some localCycle00237 else none) else (if id = 238 then some localCycle00238 else none)) else (if id < 240 then (if id = 239 then some localCycle00239 else none) else (if id < 241 then (if id = 240 then some localCycle00240 else none) else (if id = 241 then some localCycle00241 else none)))))) else (if id < 251 then (if id < 246 then (if id < 244 then (if id < 243 then (if id = 242 then some localCycle00242 else none) else (if id = 243 then some localCycle00243 else none)) else (if id < 245 then (if id = 244 then some localCycle00244 else none) else (if id = 245 then some localCycle00245 else none))) else (if id < 248 then (if id < 247 then (if id = 246 then some localCycle00246 else none) else (if id = 247 then some localCycle00247 else none)) else (if id < 249 then (if id = 248 then some localCycle00248 else none) else (if id < 250 then (if id = 249 then some localCycle00249 else none) else (if id = 250 then some localCycle00250 else none))))) else (if id < 256 then (if id < 253 then (if id < 252 then (if id = 251 then some localCycle00251 else none) else (if id = 252 then some localCycle00252 else none)) else (if id < 254 then (if id = 253 then some localCycle00253 else none) else (if id < 255 then (if id = 254 then some localCycle00254 else none) else (if id = 255 then some localCycle00255 else none)))) else (if id < 258 then (if id < 257 then (if id = 256 then some localCycle00256 else none) else (if id = 257 then some localCycle00257 else none)) else (if id < 259 then (if id = 258 then some localCycle00258 else none) else (if id < 260 then (if id = 259 then some localCycle00259 else none) else (if id = 260 then some localCycle00260 else none))))))) else (if id < 280 then (if id < 270 then (if id < 265 then (if id < 263 then (if id < 262 then (if id = 261 then some localCycle00261 else none) else (if id = 262 then some localCycle00262 else none)) else (if id < 264 then (if id = 263 then some localCycle00263 else none) else (if id = 264 then some localCycle00264 else none))) else (if id < 267 then (if id < 266 then (if id = 265 then some localCycle00265 else none) else (if id = 266 then some localCycle00266 else none)) else (if id < 268 then (if id = 267 then some localCycle00267 else none) else (if id < 269 then (if id = 268 then some localCycle00268 else none) else (if id = 269 then some localCycle00269 else none))))) else (if id < 275 then (if id < 272 then (if id < 271 then (if id = 270 then some localCycle00270 else none) else (if id = 271 then some localCycle00271 else none)) else (if id < 273 then (if id = 272 then some localCycle00272 else none) else (if id < 274 then (if id = 273 then some localCycle00273 else none) else (if id = 274 then some localCycle00274 else none)))) else (if id < 277 then (if id < 276 then (if id = 275 then some localCycle00275 else none) else (if id = 276 then some localCycle00276 else none)) else (if id < 278 then (if id = 277 then some localCycle00277 else none) else (if id < 279 then (if id = 278 then some localCycle00278 else none) else (if id = 279 then some localCycle00279 else none)))))) else (if id < 289 then (if id < 284 then (if id < 282 then (if id < 281 then (if id = 280 then some localCycle00280 else none) else (if id = 281 then some localCycle00281 else none)) else (if id < 283 then (if id = 282 then some localCycle00282 else none) else (if id = 283 then some localCycle00283 else none))) else (if id < 286 then (if id < 285 then (if id = 284 then some localCycle00284 else none) else (if id = 285 then some localCycle00285 else none)) else (if id < 287 then (if id = 286 then some localCycle00286 else none) else (if id < 288 then (if id = 287 then some localCycle00287 else none) else (if id = 288 then some localCycle00288 else none))))) else (if id < 294 then (if id < 291 then (if id < 290 then (if id = 289 then some localCycle00289 else none) else (if id = 290 then some localCycle00290 else none)) else (if id < 292 then (if id = 291 then some localCycle00291 else none) else (if id < 293 then (if id = 292 then some localCycle00292 else none) else (if id = 293 then some localCycle00293 else none)))) else (if id < 296 then (if id < 295 then (if id = 294 then some localCycle00294 else none) else (if id = 295 then some localCycle00295 else none)) else (if id < 297 then (if id = 296 then some localCycle00296 else none) else (if id < 298 then (if id = 297 then some localCycle00297 else none) else (if id = 298 then some localCycle00298 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 5, 1]], proof := .tail 17 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1664)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 3, 6, 2, 1], ![4, 0, 3, 5, 2, 1]], proof := .tail 297 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1665)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 6, 3, 1, 2], ![4, 0, 5, 3, 1, 2]], proof := .tail 45 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1666)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 6, 3, 1, 2], ![4, 0, 5, 3, 2, 1]], proof := .tail 45 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1667)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 6, 5, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 6, 3, 2, 1], ![4, 0, 5, 3, 2, 1]], proof := .tail 265 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1668)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 5, 6, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 1, 5, 6, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 2, 1, 3, 6], ![4, 0, 2, 1, 3, 5]], proof := .low6 (![101, 61, 35, 271, 184, 200, 262, 105, 58, 235, 49, 135, 175, 4, 228, 24, 160, 285, 177, 298, 131, 208, 250, 15, 174, 103, 218, 74]) }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1669)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 5, 6, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 2, 1, 6, 3], ![4, 0, 2, 1, 5, 3]], proof := .low6 (![101, 61, 35, 271, 266, 222, 287, 69, 189, 42, 214, 257, 48, 4, 31, 26, 257, 79, 239, 178, 257, 138, 224, 257, 275, 152, 60, 257]) }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1670)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 6, 5, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 2, 6, 1, 3], ![4, 0, 2, 5, 1, 3]], proof := .low6 (![101, 46, 267, 145, 166, 167, 225, 89, 205, 263, 64, 230, 48, 180, 223, 7, 161, 185, 286, 259, 53, 81, 0, 182, 223, 226, 117, 195]) }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1671)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 6, 2, 1, 3], ![4, 0, 5, 2, 1, 3]], proof := .tail 63 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1672)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 3, 5, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 6, 1, 5, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 2, 6, 1, 3], ![4, 0, 2, 5, 3, 1]], proof := .tail 113 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1673)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 3, 5, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 1, 5, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 6, 2, 1, 3], ![4, 0, 5, 2, 3, 1]], proof := .tail 290 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1674)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 3, 5, 4, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 1, 5, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 6, 2, 1, 3], ![4, 0, 5, 3, 2, 1]], proof := .tail 113 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1675)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 3, 6, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 5, 1, 6, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 2, 3, 1, 6], ![4, 0, 2, 1, 3, 5]], proof := .tail 92 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1676)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 3, 6, 4, 2], ![0, 5, 3, 6, 4, 1], ![0, 5, 2, 1, 6, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 3, 2, 1, 6], ![4, 0, 2, 1, 3, 5]], proof := .low6 (![101, 61, 35, 110, 136, 66, 261, 105, 58, 235, 49, 75, 229, 4, 228, 204, 75, 130, 177, 298, 75, 130, 169, 75, 59, 97, 1, 75]) }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1677)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 3, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 5, 6, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 2, 3, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 157 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1678)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 3, 4, 2], ![0, 5, 3, 6, 4, 1], ![0, 5, 2, 6, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 3, 2, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 56 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1679)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 3, 4, 2], ![0, 5, 6, 3, 4, 1], ![0, 5, 6, 2, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 5]], proof := .low6 (![154, 255, 215, 37, 242, 176, 207, 82, 38, 219, 203, 234, 234, 256, 276, 119, 194, 194, 68, 277, 139, 139, 249, 216, 146, 50, 112, 294]) }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1680)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 5, 6, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 2, 3, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 21 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1681)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 6, 5, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 2, 6, 3, 1], ![4, 0, 2, 5, 3, 1]], proof := .tail 162 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1682)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 5, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 6, 2, 3, 1], ![4, 0, 5, 2, 3, 1]], proof := .tail 93 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1683)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 4, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 5, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 6, 2, 3, 1], ![4, 0, 5, 3, 2, 1]], proof := .tail 19 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1684)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 4, 2], ![0, 5, 3, 6, 4, 1], ![0, 5, 2, 6, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 3, 2, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 14 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1685)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 4, 2], ![0, 5, 6, 3, 4, 1], ![0, 5, 6, 2, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 5, 1]], proof := .tail 206 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1686)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 1], ![0, 5, 6, 2, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 3, 6, 2, 1], ![4, 0, 3, 5, 2, 1]], proof := .tail 2 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1687)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 1], ![0, 6, 5, 2, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 6, 3, 2, 1], ![4, 0, 5, 3, 2, 1]], proof := .tail 162 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1688)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![0, 5, 6, 4, 1, 2], ![5, 6, 0, 3, 2, 1], ![4, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 5]], proof := .tail 9 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1689)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 4, 3, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 5, 6, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 2, 3, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 179 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1690)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 4, 3, 2], ![0, 5, 3, 6, 4, 1], ![0, 5, 2, 6, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 3, 2, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 109 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1691)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 3, 4, 1], ![0, 5, 6, 2, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 5]], proof := .tail 132 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1692)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![0, 5, 6, 4, 2, 1], ![5, 6, 0, 3, 2, 1], ![4, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 5]], proof := .tail 44 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1693)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![0, 5, 6, 4, 1, 2], ![5, 6, 0, 3, 2, 1], ![4, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 5, 1]], proof := .tail 236 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1694)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![0, 5, 6, 4, 1, 2], ![5, 6, 0, 3, 2, 1], ![4, 0, 3, 6, 2, 1], ![4, 0, 3, 5, 2, 1]], proof := .tail 98 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1695)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![0, 6, 5, 4, 1, 2], ![5, 6, 0, 3, 2, 1], ![4, 0, 6, 3, 2, 1], ![4, 0, 5, 3, 2, 1]], proof := .tail 78 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1696)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 5, 6, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 2, 3, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 227 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1697)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 6, 5, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 2, 6, 3, 1], ![4, 0, 2, 5, 3, 1]], proof := .tail 246 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1698)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 5, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 6, 2, 3, 1], ![4, 0, 5, 2, 3, 1]], proof := .tail 88 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1699)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 5, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 6, 2, 3, 1], ![4, 0, 5, 3, 2, 1]], proof := .tail 186 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1700)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 5, 3, 6, 4, 1], ![0, 5, 2, 6, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 3, 2, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 114 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1701)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 3, 4, 1], ![0, 5, 6, 2, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 5, 1]], proof := .tail 132 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1702)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 3, 4, 1], ![0, 5, 6, 2, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 3, 6, 2, 1], ![4, 0, 3, 5, 2, 1]], proof := .tail 158 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1703)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 3, 4, 1], ![0, 6, 5, 2, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 6, 3, 2, 1], ![4, 0, 5, 3, 2, 1]], proof := .tail 134 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1704)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![0, 5, 6, 4, 2, 1], ![5, 6, 0, 3, 2, 1], ![4, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 5, 1]], proof := .tail 44 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1705)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![0, 5, 6, 4, 2, 1], ![5, 6, 0, 3, 2, 1], ![4, 0, 3, 6, 2, 1], ![4, 0, 3, 5, 2, 1]], proof := .tail 10 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1706)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![0, 6, 5, 4, 2, 1], ![5, 6, 0, 3, 2, 1], ![4, 0, 6, 3, 2, 1], ![4, 0, 5, 3, 2, 1]], proof := .tail 196 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1707)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 3, 6, 5, 4], ![0, 1, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 0, 1, 2, 3]], proof := .low6 (![153, 34, 278, 18, 143, 13, 155, 187, 16, 115, 171, 197, 12, 252, 30, 30, 30, 30, 141, 244, 238, 91, 231, 201, 220, 83, 240, 72]) }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1708)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 3, 5, 4], ![0, 1, 6, 2, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 0, 1, 3, 2]], proof := .tail 291 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1709)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 3, 2], ![4, 5, 0, 1, 3, 2]], proof := .tail 76 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1710)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 0, 1, 3, 2], ![4, 5, 0, 1, 3, 2]], proof := .tail 29 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1711)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 3, 2, 6, 5, 4], ![0, 3, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 0, 1, 2, 3]], proof := .low6 (![153, 34, 278, 18, 292, 6, 90, 187, 16, 115, 171, 85, 5, 252, 30, 30, 85, 30, 141, 244, 85, 91, 231, 85, 220, 70, 57, 85]) }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1712)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 0, 3, 1, 2]], proof := .tail 113 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1713)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 3, 2], ![4, 5, 0, 3, 1, 2]], proof := .tail 147 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1714)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 0, 1, 3, 2], ![4, 5, 0, 3, 1, 2]], proof := .tail 280 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1715)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 3, 1, 2], ![4, 5, 0, 3, 1, 2]], proof := .tail 162 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1716)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 0, 3, 1, 2], ![4, 5, 0, 3, 1, 2]], proof := .tail 144 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1717)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 0, 3, 1, 2], ![4, 5, 0, 3, 1, 2]], proof := .tail 45 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1718)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 3, 6, 2, 5, 4], ![0, 3, 6, 1, 5, 4], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 0, 2, 1, 3]], proof := .tail 151 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1719)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 0, 3, 2, 1]], proof := .tail 260 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1720)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 3, 2], ![4, 5, 0, 3, 2, 1]], proof := .tail 147 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1721)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 0, 1, 3, 2], ![4, 5, 0, 3, 2, 1]], proof := .tail 280 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1722)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 3, 2, 5, 4], ![0, 3, 6, 1, 5, 4], ![0, 2, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 0, 2, 3, 1]], proof := .tail 290 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1723)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 3, 2, 5, 4], ![0, 6, 3, 1, 5, 4], ![0, 6, 2, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 0, 3, 2, 1]], proof := .tail 62 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1724)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 3, 1, 2], ![4, 5, 0, 3, 2, 1]], proof := .tail 162 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1725)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 0, 3, 1, 2], ![4, 5, 0, 3, 2, 1]], proof := .tail 144 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1726)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 0, 3, 1, 2], ![4, 5, 0, 3, 2, 1]], proof := .tail 45 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1727)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 3, 6, 5, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 1, 3], ![4, 5, 0, 2, 1, 3]], proof := .tail 137 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1728)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 3, 5, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 1, 3], ![4, 5, 0, 2, 3, 1]], proof := .tail 137 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1729)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 3, 5, 2, 4], ![0, 6, 3, 5, 1, 4], ![0, 6, 2, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 1, 3], ![4, 5, 0, 3, 2, 1]], proof := .tail 264 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1730)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 3, 4], ![0, 6, 5, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 3, 2, 1], ![4, 5, 0, 3, 2, 1]], proof := .tail 28 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1731)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 4, 3], ![0, 6, 5, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 0, 3, 2, 1], ![4, 5, 0, 3, 2, 1]], proof := .tail 144 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1732)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 3, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 6, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 3, 1], ![4, 5, 0, 2, 3, 1]], proof := .tail 93 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1733)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 3, 2, 4], ![0, 6, 3, 5, 1, 4], ![0, 6, 2, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 3, 1], ![4, 5, 0, 3, 2, 1]], proof := .tail 19 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1734)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 1, 4], ![0, 6, 5, 2, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 3, 2, 1], ![4, 5, 0, 3, 2, 1]], proof := .tail 142 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1735)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 6, 5, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 0, 3, 2, 1], ![4, 5, 0, 3, 2, 1]], proof := .tail 265 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1736)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 2, 1, 3], ![4, 6, 0, 2, 1, 3], ![4, 5, 0, 2, 1, 3]], proof := .tail 273 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1737)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 3, 5, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 1, 5, 4], ![5, 6, 0, 2, 1, 3], ![4, 6, 0, 2, 1, 3], ![4, 5, 0, 2, 3, 1]], proof := .tail 290 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1738)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 3, 5, 4, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 1, 5, 4], ![5, 6, 0, 2, 1, 3], ![4, 6, 0, 2, 1, 3], ![4, 5, 0, 3, 2, 1]], proof := .tail 113 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1739)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 3, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 5, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 6, 0, 2, 3, 1], ![4, 5, 0, 2, 3, 1]], proof := .tail 93 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1740)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 3, 4, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 5, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 6, 0, 2, 3, 1], ![4, 5, 0, 3, 2, 1]], proof := .tail 19 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1741)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 1], ![0, 6, 5, 2, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 6, 0, 3, 2, 1], ![4, 5, 0, 3, 2, 1]], proof := .tail 162 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1742)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![0, 6, 5, 4, 1, 2], ![5, 6, 0, 3, 2, 1], ![4, 6, 0, 3, 2, 1], ![4, 5, 0, 3, 2, 1]], proof := .tail 78 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1743)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 4, 3, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 5, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 6, 0, 2, 3, 1], ![4, 5, 0, 2, 3, 1]], proof := .tail 88 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1744)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 5, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 6, 0, 2, 3, 1], ![4, 5, 0, 3, 2, 1]], proof := .tail 186 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1745)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 3, 4, 1], ![0, 6, 5, 2, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 6, 0, 3, 2, 1], ![4, 5, 0, 3, 2, 1]], proof := .tail 134 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1746)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![0, 6, 5, 4, 2, 1], ![5, 6, 0, 3, 2, 1], ![4, 6, 0, 3, 2, 1], ![4, 5, 0, 3, 2, 1]], proof := .tail 36 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1747)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 3, 6, 5, 4], ![0, 1, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 0, 1, 2, 3]], proof := .low6 (![106, 241, 281, 11, 248, 13, 155, 270, 191, 159, 32, 148, 296, 54, 209, 80, 258, 237, 254, 140, 22, 12, 3, 47, 12, 77, 27, 72]) }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1748)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 3, 5, 4], ![0, 1, 6, 2, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 0, 1, 3, 2]], proof := .tail 43 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1749)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 3, 2], ![5, 4, 0, 1, 3, 2]], proof := .tail 71 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1750)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 0, 1, 3, 2], ![5, 4, 0, 1, 3, 2]], proof := .tail 274 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1751)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 3, 2, 6, 5, 4], ![0, 3, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 0, 1, 2, 3]], proof := .low6 (![106, 241, 281, 11, 292, 6, 90, 270, 191, 159, 32, 85, 41, 54, 209, 80, 85, 237, 254, 140, 85, 5, 3, 85, 5, 70, 57, 85]) }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1752)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 0, 3, 1, 2]], proof := .low6 (![293, 125, 210, 20, 87, 164, 126, 96, 217, 104, 121, 107, 283, 102, 181, 211, 40, 232, 289, 193, 212, 272, 67, 100, 55, 123, 25, 86]) }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1753)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 3, 2], ![5, 4, 0, 3, 1, 2]], proof := .tail 202 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1754)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 0, 1, 3, 2], ![5, 4, 0, 3, 1, 2]], proof := .tail 94 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1755)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 3, 1, 2], ![5, 4, 0, 3, 1, 2]], proof := .tail 233 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1756)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 0, 3, 1, 2], ![5, 4, 0, 3, 1, 2]], proof := .tail 23 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1757)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 0, 3, 1, 2], ![5, 4, 0, 3, 1, 2]], proof := .tail 118 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1758)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 3, 6, 2, 5, 4], ![0, 3, 6, 1, 5, 4], ![0, 2, 1, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 0, 2, 1, 3]], proof := .low6 (![221, 150, 269, 8, 213, 167, 95, 111, 99, 122, 168, 33, 33, 288, 39, 243, 279, 279, 156, 120, 129, 133, 253, 124, 124, 165, 188, 149]) }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1759)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 0, 3, 2, 1]], proof := .tail 183 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1760)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 3, 2], ![5, 4, 0, 3, 2, 1]], proof := .tail 202 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1761)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 0, 1, 3, 2], ![5, 4, 0, 3, 2, 1]], proof := .tail 245 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1762)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 3, 2, 5, 4], ![0, 3, 6, 1, 5, 4], ![0, 2, 6, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 0, 2, 3, 1]], proof := .tail 173 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1763)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 3, 2, 5, 4], ![0, 6, 3, 1, 5, 4], ![0, 6, 2, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 0, 3, 2, 1]], proof := .tail 65 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1764)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 3, 1, 2], ![5, 4, 0, 3, 2, 1]], proof := .tail 84 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1765)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 0, 3, 1, 2], ![5, 4, 0, 3, 2, 1]], proof := .tail 23 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1766)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 0, 3, 1, 2], ![5, 4, 0, 3, 2, 1]], proof := .tail 118 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1767)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 3, 6, 5, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 1, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 1, 3], ![5, 4, 0, 2, 1, 3]], proof := .tail 170 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1768)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 3, 5, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 6, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 1, 3], ![5, 4, 0, 2, 3, 1]], proof := .tail 198 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1769)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 3, 5, 2, 4], ![0, 6, 3, 5, 1, 4], ![0, 6, 2, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 1, 3], ![5, 4, 0, 3, 2, 1]], proof := .tail 284 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1770)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 3, 4], ![0, 6, 5, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 3, 2, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 128 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1771)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 4, 3], ![0, 6, 5, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 0, 3, 2, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 268 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1772)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 3, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 6, 5, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 3, 1], ![5, 4, 0, 2, 3, 1]], proof := .tail 199 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1773)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 3, 2, 4], ![0, 6, 3, 5, 1, 4], ![0, 6, 2, 5, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 3, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 51 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1774)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 1, 4], ![0, 6, 5, 2, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 3, 2, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 163 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1775)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 6, 5, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 0, 3, 2, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 251 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1776)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 1, 6, 5, 4], ![6, 5, 0, 2, 1, 3], ![6, 4, 0, 2, 1, 3], ![5, 4, 0, 2, 1, 3]], proof := .tail 52 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1777)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 3, 5, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 1, 5, 4], ![6, 5, 0, 2, 1, 3], ![6, 4, 0, 2, 1, 3], ![5, 4, 0, 2, 3, 1]], proof := .tail 295 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1778)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 3, 5, 4, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 1, 5, 4], ![6, 5, 0, 2, 1, 3], ![6, 4, 0, 2, 1, 3], ![5, 4, 0, 3, 2, 1]], proof := .tail 52 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1779)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 3, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 5, 1, 4], ![6, 5, 0, 2, 1, 3], ![6, 4, 0, 2, 3, 1], ![5, 4, 0, 2, 3, 1]], proof := .tail 199 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1780)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 3, 4, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 5, 1, 4], ![6, 5, 0, 2, 1, 3], ![6, 4, 0, 2, 3, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 51 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1781)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 1], ![0, 6, 5, 2, 1, 4], ![6, 5, 0, 2, 1, 3], ![6, 4, 0, 3, 2, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 233 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1782)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![0, 6, 5, 4, 1, 2], ![6, 5, 0, 3, 2, 1], ![6, 4, 0, 3, 2, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 247 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1783)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 4, 3, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 5, 4, 1], ![6, 5, 0, 2, 3, 1], ![6, 4, 0, 2, 3, 1], ![5, 4, 0, 2, 3, 1]], proof := .tail 282 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1784)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 5, 4, 1], ![6, 5, 0, 2, 3, 1], ![6, 4, 0, 2, 3, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 192 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1785)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 3, 4, 1], ![0, 6, 5, 2, 4, 1], ![6, 5, 0, 2, 3, 1], ![6, 4, 0, 3, 2, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 172 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1786)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![0, 6, 5, 4, 2, 1], ![6, 5, 0, 3, 2, 1], ![6, 4, 0, 3, 2, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 108 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1787)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 6, 3, 4, 5], ![0, 2, 6, 3, 4, 5], ![0, 1, 6, 3, 4, 5], ![6, 0, 1, 2, 4, 5], ![6, 0, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 0, 1, 2]], proof := .tail 127 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1788)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 6, 3, 4, 5], ![0, 2, 6, 3, 4, 5], ![0, 1, 6, 3, 4, 5], ![6, 0, 1, 2, 5, 4], ![6, 0, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 3, 0, 1, 2]], proof := .tail 73 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1789)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 6, 3, 4, 5], ![0, 2, 6, 3, 4, 5], ![0, 1, 6, 3, 5, 4], ![6, 0, 1, 2, 5, 4], ![6, 0, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 4, 3, 0, 1, 2]], proof := .tail 116 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1790)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 6, 3, 4, 5], ![0, 2, 6, 3, 4, 5], ![0, 1, 6, 5, 3, 4], ![6, 0, 1, 5, 2, 4], ![6, 0, 1, 5, 2, 3], ![6, 0, 1, 4, 3, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 190 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1791)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (1664 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 1664 ≤ id.val) (hhigh : id.val < 1792) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 1664)) = true := by
  let j : Fin 128 := ⟨id.val - 1664, by omega⟩
  have hsum : 1664 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (1664 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard013
