import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard018
open N4R2RowDataReplay

-- Original cycle 024d6a97dc02f9ba69cc2cb6cacc202e3ac8da61d4a611bbc3fb6b3a5d4920f2; original global index 183.
def localCycle00000 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 02b78bb468c5ab24d71199a4ba4da5136e42ad976e0949d5459cb1eaa8a718d7; original global index 213.
def localCycle00001 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .gapLower 1 4, .triangle 16 2, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 02d77aa919c3c87e314939fe60f84294915a1213fd9a56e2edfc3c3078367f71; original global index 228.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .triangle 23 1, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 035a16a2dfedfaff48a980c9b71b00fa9897eec4047a25138f5aec3c14826ad3; original global index 272.
def localCycle00003 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 3, .gapUpper 3 4, .gapLower 6 4, .triangle 18 0]

-- Original cycle 045177addd8632b6124533fe8877185d39e178582f6b5af61a0fece59458aad1; original global index 341.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 2, .triangle 14 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 05dbcbf0543f500c48e20b9c27d9a6a5cdc5adb4e31f9ce3bce97674fda93b1f; original global index 486.
def localCycle00005 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 08b621d0e51795bd0794ec4cd90a213238dd788adb073d5a91a6e7dafda83974; original global index 697.
def localCycle00006 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 08ba462e7b75c10c71167966bcc5d900bfd4ee9aac292875020f7dad3b30961e; original global index 700.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 11 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 08e44447aad0793e2147eddcca6e6932562b130143f0b5780514828cf1931bff; original global index 709.
def localCycle00008 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 22 1, .triangle 23 0, .triangle 34 1, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 0aec698d35f05de61f2a66e02f5abeee3251961358a462214fa6fdbbb57146c2; original global index 874.
def localCycle00009 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 0b9f9057c5f5b24d2a95667fc97881f115252165b78b27fd33f994edfc7d6f1c; original global index 931.
def localCycle00010 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 0, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 0dd51822c6ffd60e4cca8c4a1462fe132e7e796970b47ba353e736b938d93c68; original global index 1089.
def localCycle00011 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 0f08c886f93e3c63581cbbd3bb4c911f3e1e40a26cfd6e2a32e4e1c10ca24050; original global index 1193.
def localCycle00012 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 5, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 26 0, .triangle 33 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 116985dcd8e2f7b9b23f3ffcbf3a423769a819d9305817bf59c18e7360a4829f; original global index 1388.
def localCycle00013 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 2, .triangle 24 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 12af27228b5f0d72f8e2f57f49e83d6d1ebe2e97b1d1290acb09ff005fffad6e; original global index 1476.
def localCycle00014 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 13ca43ce2f19cdbe00caea30a978ac43133feaaf8bc6a9035d1d45391b1afb64; original global index 1571.
def localCycle00015 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 156b777143e47af89725913aaccc1759e20ee561de4259c78bbed3f3d93f30cb; original global index 1696.
def localCycle00016 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 2, .gapUpper 5 2]

-- Original cycle 15c33039c5db969f7fd4105a47785367d75ef1ab613eda43fc9787afb877da43; original global index 1729.
def localCycle00017 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 18efb696cf76f5c0d6612296f007533143747b72fb9f7dbf29cff7b5ba47ac47; original global index 1947.
def localCycle00018 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 31 2, .triangle 33 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 191ee014448898640ed72f7379db588e12e6a64d14ec3a61a26925cb43f4a970; original global index 1959.
def localCycle00019 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 1a99d4b966fdff1e815556a43b763ef3372fb9ce6fe251b6803c00b4deb4a428; original global index 2069.
def localCycle00020 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, -2, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .gapUpper 3 6, .thetaLower 3]

-- Original cycle 1aa694e1a96d0d3caaabb5cacae865be68f61483fae82f2f5a8ff0eaf31173a4; original global index 2072.
def localCycle00021 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 0, .triangle 30 0, .triangle 7 2, .triangle 10 1, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 1b06d0a55d876553a1f91987dff93442a2ede03a8bc746da5203ee4233fd9441; original global index 2091.
def localCycle00022 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -2, -2, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle 1b22f9d5826a3df8723c800032e9bc79a84534470e16dd1fc19b6b2e9c519eb8; original global index 2099.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 10 1, .triangle 9 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 1bce0178da63d3fe188213a33140db3a45114013f027ec810f90473c6fc853cc; original global index 2149.
def localCycle00024 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 3, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .gapLower 3 2, .gapLower 0 3, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 1d57e8993dc74ff4bb331514755a5d89a422dae34c79f20cd7bedf3bce16a7b9; original global index 2258.
def localCycle00025 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 1dcd285e8a6a86df4cd2cc9da420ed48fbfbff4865b261f31d4ebe0ea6e9e72c; original global index 2289.
def localCycle00026 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 1fb06be5f126507488c1e85b7e4dc963a89842a25e7b8d3ff2d6ce106427c9de; original global index 2438.
def localCycle00027 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 203eb9f12f55c8269ec00b563ba4464b8d51969c1b9f4c88256fcf9e7d843c0b; original global index 2470.
def localCycle00028 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 2 6, .distance 0 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 2, .gapLower 6 2, .triangle 8 2, .gapLower 6 0]

-- Original cycle 20511e8ac3f85a3ee9effa9bc538e39a0b198970598ee2197f7d320a72571cf5; original global index 2476.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 21d3f865096735ff423e431cc7c3f5c41a37524cfe3acb983ee23053069e334e; original global index 2594.
def localCycle00030 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 4 3, .gapLower 4 2, .gapLower 0 2, .gapLower 0 1]

-- Original cycle 220af825b8c86d8d807f401a2ae276101fb643db8316f92f370eaa0496b7a948; original global index 2608.
def localCycle00031 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4]

-- Original cycle 2312278b2ecee82e99645649eb6a14b0fd818a33a7c6c3b334789a78dc8a8470; original global index 2689.
def localCycle00032 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 34 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 234892d0b69ba6552ace4faa254b0876627355689920cc9b4fddbfbb570d063c; original global index 2704.
def localCycle00033 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 5, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, -2, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .gapUpper 5 0, .gapLower 0 4, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 26004472aa7614bb11b08a3194fab83b66a1066424bca6e3c22899129c2fe7c9; original global index 2913.
def localCycle00034 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .gapLower 0 4, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 288dbf1cdabb12933fdb3733353c8c3813fd64e769da452f42dd021540910809; original global index 3103.
def localCycle00035 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 3, .triangle 5 0, .triangle 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 28fb18146943844d1089453cc93b0d2ce9596856f10b320e168fcec4b1cad9ba; original global index 3134.
def localCycle00036 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 2958fb68c875ad3854699bdb4e1a014a9915ca8a8d6a576cf8d831eedce3f2b6; original global index 3155.
def localCycle00037 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 29a9d9132bec99606111fe730c0badd1c79d51c779c5c7da452adc4edd99d111; original global index 3180.
def localCycle00038 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 3051e5d4b634492b8b291c96991aca72b90d12378e19cf3e29b4e18289c9d3fa; original global index 3679.
def localCycle00039 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 2 1, .gapLower 4 2, .gapLower 0 2]

-- Original cycle 3235f8fa7211c095d90fabe0b853861de98a0c00ceb5a1347cc147dbc53b9079; original global index 3834.
def localCycle00040 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 26 2, .triangle 28 1, .triangle 29 0, .triangle 34 1, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 333c9e812a4e4736a8caf1d5cad3e116b4051553e8b7e411eb5b03b4bcf0e1f5; original global index 3919.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 30 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 33d49523e6a4710ded22088319f15a549d467f0f003b6fd824d74af9d7f83f89; original global index 3972.
def localCycle00042 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 16 2, .gapUpper 4 4, .triangle 32 2, .triangle 27 0, .triangle 15 0]

-- Original cycle 340283654a1e58fbd16595e447d0183eca017914b753ab042e6474cd079afe96; original global index 3986.
def localCycle00043 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 3414eb90576984ff11aa9b321096d95cf7a643da552a5c45dfd780adbbb0244b; original global index 3992.
def localCycle00044 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, 0, -3, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapUpper 3 6, .thetaLower 3]

-- Original cycle 370234b0330fd835058f7125853eb389f6a58749a478b9d1b71ed74b206423ff; original global index 4221.
def localCycle00045 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 25 2, .gapLower 4 2, .gapLower 0 2, .triangle 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 3702df67174d5eb887eb9533283ebf2e86aa162f182e9a6c4016e3526e682199; original global index 4222.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 393f5dce4c35096d60baa06bd8dfa71374b39ca36f6518231c17a82160d4651c; original global index 4404.
def localCycle00047 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 4 6, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 34 1]

-- Original cycle 3a1b7a1d169bd400c45f64a8f5056d8ad0e65d46e3e508141f38ed113f07737f; original global index 4484.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 4]
    constant := ![4, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 34 0, .triangle 33 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 25 0, .gapLower 4 0]

-- Original cycle 3b5d5c7a09f61ad21a1082816e915de55c2ca8fb5f0ba0869ab7bcd29a0fff67; original global index 4589.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 3d5dc0b1b3e4a572382239c585bae996320b485d3ff6d1629d0685927c666599; original global index 4751.
def localCycle00050 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 3ee23f681fcdf9490151e8a3c12d9aa8a143b96491094ed648e95e58778f94f4; original global index 4862.
def localCycle00051 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 23 2, .gapLower 6 2, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 3fc40dfee9394bad3ffeb37a59ab1e92103595a779c2e9217932e70a90f0a5c8; original global index 4924.
def localCycle00052 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 404324fbeab58d95bf12b8e500744c1c1af23103d27d3dea328c462ebf6fe16b; original global index 4963.
def localCycle00053 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 4255380feb8fc5073154902e0d193607b8ce3a2134764c4776b0c2f2d624e660; original global index 5108.
def localCycle00054 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 25 2, .gapLower 4 2, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 4266614f088427d2b310ee8dd047b93443adb68d18d6e0a7e145e2accabdea64; original global index 5115.
def localCycle00055 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 24 1, .gapLower 6 1, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 43bd51f7fa27940af8c793dd819e9bdfbc94cbb98975ca3f8fa78e30511f8609; original global index 5241.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 44633a6873ab2a519c1b8346d4954651d407ca8533ddad2b55d40d8ed2ff24f4; original global index 5296.
def localCycle00057 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .gapLower 6 2, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 486b414d69433d798bfcd312107682365d31caaa95468221d735a8009882cf59; original global index 5606.
def localCycle00058 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 2 5, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -2, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 30 1, .gapLower 5 1, .gapLower 0 4, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 49078b9fa37f95494694157ace15ea1b483f696698a1414121f8bddb220a54c2; original global index 5655.
def localCycle00059 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 4a373a4c2889d846287b363f8f6f788ccce42dbafd8d13da1085dc773591f051; original global index 5754.
def localCycle00060 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 4bce7ac1fe80a03c238efbe677828241ac098f17048c59daaf12f336b05bf663; original global index 5887.
def localCycle00061 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 2]
    constant := ![-1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.triangle 16 0, .triangle 29 0, .triangle 32 2, .gapUpper 3 3, .gapLower 1 4]

-- Original cycle 4ce919da905b0b7463f8b0302b38a4bdefc8d21b3652b550a148a29d5ab55506; original global index 5974.
def localCycle00062 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 6, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -3, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .gapLower 6 1, .triangle 11 1, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 4de4a42e1d42e03e87aae2c5606f0dab5a317f02c4c69275e0bf63130387842e; original global index 6047.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .triangle 15 0, .triangle 5 2, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 4eed0834ef489cf7bda70c43372c3e2e7c0e7679366930ed4722cf85a11d025f; original global index 6132.
def localCycle00064 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 3, .gapUpper 3 4, .gapLower 6 4, .triangle 18 0]

-- Original cycle 52030e3745834a2e3081a0f35d2cbda86205a1c0cabe09ba5b860dfb73e52183; original global index 6378.
def localCycle00065 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 28 2, .triangle 17 0, .triangle 16 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 52a180397a1622026716a8806c41efd0937a448502e99bc52702fffe17fa3bf2; original global index 6421.
def localCycle00066 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 536d9b8e6a9a87188e28249b321185772872c53bb19cf8abe570191d6f6f64eb; original global index 6483.
def localCycle00067 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 5, .distance 0 5, .distance 0 3, .distance 0 4, .theta 0, .zero]
    constant := ![0, 2, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .gapUpper 5 0, .gapLower 0 4, .gapLower 0 3, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 5535414978d09853ea420ca106b130e398f17c676b4ba2fdbb4fc1e76998b27a; original global index 6597.
def localCycle00068 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 55e90d2d4363f5b4a4a7e4fd45233d114e4ea00ff12b92647ce93477f308145c; original global index 6660.
def localCycle00069 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 26 0, .triangle 5 2, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 55f1969fb7fcda6b0cc66f6b990bbd62453fd5dea3f167422d712d37248e5749; original global index 6664.
def localCycle00070 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 26 1, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 57a27f30dd467780d9c2e3903833d2257e1bbe890490940b38638c687f6af88e; original global index 6802.
def localCycle00071 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 4 3, .triangle 6 0, .gapLower 0 1]

-- Original cycle 5abaf0028ecf83dafa5402b8511784ef01c8b4ea6034b33851a466d7c0957a03; original global index 7064.
def localCycle00072 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 2, .gapLower 0 5, .gapLower 0 4, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 5bca68d3dbf46d54509ea07cac617e443289327ed1c4f15cda5066eab984da4f; original global index 7134.
def localCycle00073 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 17 0, .triangle 15 0, .triangle 27 0, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 5e9d348df1212f9d94801397a756b9e8e43fc62f0e6243bc876b988d9856a847; original global index 7357.
def localCycle00074 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 5ebe9362b2d027bc3339b5220610768e0bd83de7891492731cd228107295685e; original global index 7375.
def localCycle00075 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 5f5eea509974936c916e7e5defde5048c8811418c72b6e0c197bfb214409f00f; original global index 7426.
def localCycle00076 : Cycle where
  length := 4
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .theta 6]
    constant := ![3, -2, 0, -2]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 13 2, .gapLower 6 0]

-- Original cycle 60b20e0489fb1536f5236decf32746871597a6e8d1e063ac31408a0f1871a38c; original global index 7530.
def localCycle00077 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 2, .triangle 21 0, .triangle 27 0, .triangle 5 2, .triangle 9 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 610af42fa430b706f8d88f970c460613fe48bc03b99ddbc452c9f822eb45686c; original global index 7568.
def localCycle00078 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 33 0, .triangle 30 0, .gapLower 2 3, .gapLower 3 2, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 61c013adcbbdcaa017c9de286a13ddb959bb98ee90330ed2758acfa446eed26e; original global index 7629.
def localCycle00079 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 62429fa6fb88f001fece692d8517d144de013a9a1ff0fe2d132903ab8450d8c8; original global index 7669.
def localCycle00080 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 11 1, .triangle 9 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 63de5a11dba230216e081a8ae73093cf1e648fc37fba31d5a7722c42be03be2c; original global index 7783.
def localCycle00081 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 6551cda538e05892b847e12bc9f9fa1139e26cf7ab2f3ea4b5fe715014656c46; original global index 7883.
def localCycle00082 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 65be3992898c1159f77e4d4b7d63d7630b07706085fa3087fc91dbb10485eee2; original global index 7915.
def localCycle00083 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 67335d407e25d404fc8d983c9f88f5df36d66f094e37cffa7a5525acbb9bd1d1; original global index 8022.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 677b70e6bb890a87a7b678e15097069fa26ccc3208d33ba1a1d9f0646aa96221; original global index 8040.
def localCycle00085 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 16 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 6bcd5aee4ac51e03f85efec6c03ea5a0a177d72aac0dadadd31e0189de09a2e5; original global index 8397.
def localCycle00086 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 3 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 32 2, .triangle 33 1, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 6deb4ca7bef31208d819a95433433084a8e2ef321c6132e0b3862ea97b52012c; original global index 8537.
def localCycle00087 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .gapLower 6 3, .triangle 21 1]

-- Original cycle 7047371c6a6b35a93683953955ba2ebe65ddbb000261040c33df07c228dabf37; original global index 8697.
def localCycle00088 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 7536d3d71df16bc843111da1f305a143ac83519db4636fdc70b8b580198e3f72; original global index 9082.
def localCycle00089 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 21 0]

-- Original cycle 757caed086350bdc952d1210462c14aa5f47a481f09cd918753fc3bc66d2275c; original global index 9104.
def localCycle00090 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 5 0, .triangle 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 766343f43fc61480162db1a1231e128cf79279f448a4409cf7a066941e673502; original global index 9164.
def localCycle00091 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 21 2, .gapLower 6 2, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 77d8e93a7bba8f0fdb5184527c20e1b7061fc62f05a72bbd716b3539f557dbdb; original global index 9267.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .gapLower 3 0]

-- Original cycle 78659cbad7ea89190510e9f3427cb788f5c33808907b4f3773be01c7f26c9d01; original global index 9310.
def localCycle00093 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 6, .distance 2 6, .distance 0 6, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .gapLower 6 1, .triangle 14 1, .triangle 10 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 78e7a527383cd10e354bf84bdfe7ce3a16699819d5d71724aa069e183cb9bf4f; original global index 9354.
def localCycle00094 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 2 1, .gapLower 4 2, .gapLower 0 2]

-- Original cycle 7e50d2d55cf69122e83ee19a8554be4277baabd737878c31a39f2ff2deb76704; original global index 9810.
def localCycle00095 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 33 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 83986cae57bdea91fdac6464e214d58b8896ee1bbd986d9ff1f66304b33eccfd; original global index 10216.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 0, .triangle 14 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 85103b8d055dd33381eebdd5fdd1e383e7bf0340ccdfa18e9995d01bf42168db; original global index 10327.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapLower 6 2, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 86c5f5d2ea01fd3d6498d319507f86deb9cf45731b93533d202f64c18af0e416; original global index 10453.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 8755d1b94518d1d7ff2c5a5c1633173751d87297062d1008c41454a64b2fd72f; original global index 10495.
def localCycle00099 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 3, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 17 1, .triangle 15 0, .triangle 5 2, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 87b7e195241c0c86f1c6bde4693cdceaa6423f44045d3b0641ff3a04c300f95e; original global index 10520.
def localCycle00100 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 89b44eb1bb577614d1e1a22917bd893a010bd9786c4c7b5cfab02a69afc90c16; original global index 10669.
def localCycle00101 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 34 1, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 8c57e6904d9ca444305b16374bfb45d9fd2414c0f6bdc9dd36824d4aa8f241f4; original global index 10859.
def localCycle00102 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 26 0, .gapLower 3 2, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 8d1fb9adc5084dd63176c0162a1660e75199ab9b3913809a09b29f10ea85e86a; original global index 10914.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 26 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 8d4fce3d20a93085ed6e63ecf2ba827b4d68f656e6792688569a87d3ec9f5f86; original global index 10926.
def localCycle00104 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 4]
    constant := ![2, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 18 2, .triangle 23 1]

-- Original cycle 8db31dde9cd7e02cf49187c329677af6b00b49fe47c24fb5e389149ace29f4db; original global index 10961.
def localCycle00105 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 8e6128d4341334099a556838786128056d8fda7cb3944afecafd0288dfeef944; original global index 11023.
def localCycle00106 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 26 1, .triangle 27 0, .triangle 11 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 9149f6569cc2abb1952e382438b5a37c7506b4f5a094deb9342ca787d1621cab; original global index 11254.
def localCycle00107 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 5, .distance 0 5, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .gapUpper 5 0, .gapLower 0 4, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 929eedb8995cf4b7d131d31aad0034737ee57cfbbe352584189d50be7b4a80fd; original global index 11359.
def localCycle00108 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 1 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 957c03792a88374e0ccbd026d9834d3d93c0aa29dcbaab528aa77896d5b69976; original global index 11618.
def localCycle00109 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 982b3684bbee5985b3999ebdced43ac6d5981f64d64524570dbbeff44b245ef6; original global index 11820.
def localCycle00110 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 2 5, .distance 0 5, .distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 30 1, .gapLower 5 1, .gapLower 0 4, .gapLower 0 3, .gapLower 4 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 9b2748f1833be5e8030e828296292197b6e9b907ccd51f11ff2bb43327bd0ebb; original global index 12062.
def localCycle00111 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 9b558feee4e058657947596e039098cc084e51d47fdeb0352ff402bcaa32370c; original global index 12080.
def localCycle00112 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -3, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle 9b9800f2b98ab5a64b3c8b7621b8e21584e50679f7f6ed2dd79ad820e51e81a3; original global index 12105.
def localCycle00113 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 21 2, .triangle 4 2, .gapLower 6 0]

-- Original cycle 9c2928e34ce522a3e2e3f26d6d9691e978f0dcff990cafdcc2839c96bd49ce9c; original global index 12148.
def localCycle00114 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 9d2322483c862ee374f7086ce6b41666e4d65a729ca25b1e7d96a4ca77203d52; original global index 12223.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .gapLower 1 4, .triangle 17 0, .triangle 26 1, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 9e2af354e14bae4d6f2873d6fde211d8ea19e769866eee95776aefc941ae0e01; original global index 12310.
def localCycle00116 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 9ef9344b8acf87092a6f5c523db549e8dbb98e33fb477b8e59dd968b002febe8; original global index 12379.
def localCycle00117 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 9f289abb77c15de2a49231b58ecd0501cfec4350a078e3b8012830bfdf26f0f9; original global index 12392.
def localCycle00118 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle a03bc25dc41ab1b6078fa8f9429677136d50e096cc07dd77f39b9b4bc808e34e; original global index 12465.
def localCycle00119 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 29 0, .triangle 34 1, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle a1435c4762c00281b7364b0d324f83079aa02692886ee0b1210dfec5b4e30c81; original global index 12539.
def localCycle00120 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![2, 0, -1, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 4 3, .triangle 6 0, .gapLower 0 1]

-- Original cycle a1f924090682476e1a48183e70649fbdb2502ad6b53a936057ce69a526a52c6c; original global index 12596.
def localCycle00121 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 26 0, .triangle 33 0, .triangle 14 0, .triangle 10 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle a1fe57f771416b7ffa9ae228487b313f78ae31303601ccc029a4ead805606111; original global index 12597.
def localCycle00122 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 1, .gapLower 6 1, .triangle 14 1]

-- Original cycle a23ed43e3a014bc9975a4a74f9c8ba71c223a5ff8d958353ca81fdd65bbde4d2; original global index 12625.
def localCycle00123 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 5 2, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle a4cce42e079e92e4d9065f479f6055e9f01ba77f4c7398672528dbfe0575d2c0; original global index 12808.
def localCycle00124 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle a6fe51bac39ce5ed7e755131ba05e23ffd34879337f989889a2e66ff5e04fee7; original global index 12979.
def localCycle00125 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle ab6c7e4dba348ec5549d23863b3e910bbcdcfc9f369dcdbfc6a91f66c369ccde; original global index 13357.
def localCycle00126 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle adad59097e5cb9dbc8822365383e295929cfcc2d004fadf52b9e7ca0662f1de2; original global index 13556.
def localCycle00127 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .gapLower 6 3, .triangle 18 1, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle af917479f3971945e5619cd081c8c853fa46000c64f1be36bbbbc4462872fe95; original global index 13713.
def localCycle00128 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle b09a42587b490b45da4426b572337a81f828647d446adc3f60ad02b983c33a13; original global index 13790.
def localCycle00129 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -3, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 2, .gapLower 0 5, .triangle 10 1, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle b255888ce60eba02a72ee82c6a0fca5decebafeeb4087f8a949cb438c13a5acd; original global index 13938.
def localCycle00130 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 33 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4]

-- Original cycle b2ef40b259efb1576c35aecfb03dcd1d2f01e61b22bb75c232916f2f6271fe5b; original global index 13984.
def localCycle00131 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 2 6, .distance 1 2]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 18 2, .gapLower 6 2, .gapUpper 2 5]

-- Original cycle b31a47d8e15ef00271428dab393262f60c3e445f983c4f8fd374bbc72a0a27f0; original global index 13995.
def localCycle00132 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .gapLower 3 2, .gapLower 0 3, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle b4b958571eaa8e7fc597e90ebf6babd84e056ab7266a84451161fca34b121236; original global index 14112.
def localCycle00133 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 3 4, .distance 0 3]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .gapUpper 3 1]

-- Original cycle b693b8f20f30fd8d7b0ec7c72a71b4e289899079cf46242dc0e3c1c9d7cda70d; original global index 14268.
def localCycle00134 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle b8cbd51b78d7218431dbcc4f6db530667e5db6741f12a58cf05ab59a0ce7425f; original global index 14424.
def localCycle00135 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 30 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle b9faeaf1be154d10d90e50f2469ec2afbdd3c7c84a55168152605f2bbabbf570; original global index 14522.
def localCycle00136 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 2]
    constant := ![-1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.triangle 16 0, .triangle 28 0, .triangle 31 2, .gapUpper 3 3, .gapLower 1 4]

-- Original cycle bcc67225915ba129ede978df1e866a6d900eebac67d2f0c1e9b50374dc644b0a; original global index 14726.
def localCycle00137 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 17 0, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle bd7e9656b5159af002e0b04971df3863b0745475f2cf91e7fb82e4424a9c9ffc; original global index 14781.
def localCycle00138 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 1 6, .distance 1 2]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 4, .gapLower 6 3, .triangle 18 1]

-- Original cycle bd910d1a2c0766d07538c4a96c787ef30f4484bdf34b10f260440fd49d873cff; original global index 14786.
def localCycle00139 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle c0140fe255e0a7c22844f13bcd18b1965389af21c8ab242a257ab90dfdcaa34b; original global index 14993.
def localCycle00140 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 32 2, .gapUpper 3 6, .thetaLower 3]

-- Original cycle c079249653540772f03b23042654b4562ccd3c20e8689a7effe23f6a5f11fad5; original global index 15023.
def localCycle00141 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 6, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 0, .gapLower 6 1, .triangle 11 1, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle c1325e9802ea9ad7553b276c22647c71190f36372c47fb335b0c98ff84da892a; original global index 15082.
def localCycle00142 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 33 1, .triangle 26 0, .triangle 5 2, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle c6b22a550d6c0eb3ccb5b2ab5f549b6aa8414af05548c1c391d567a0edf8088b; original global index 15501.
def localCycle00143 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 2, .triangle 30 1, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle c86f25b4d26b31cd5c212b055732ecc10b13729509ba4c96aef3f82fc637263e; original global index 15651.
def localCycle00144 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 2 5, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 30 1, .gapLower 5 1, .gapLower 0 4, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle cd9a6fe0de2ff0f5e41fbbaffd101d09cbaeeceef6d0aea225441f4021450d2c; original global index 16069.
def localCycle00145 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 5, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, -3, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .gapUpper 5 0, .gapLower 0 4, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle ceffda76076353e9192fbb3248ad38d14862ecb9d95d917420d7a1c7f5a48ba4; original global index 16152.
def localCycle00146 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 0]

-- Original cycle d04414905b848fc5ad8d7d6fdb54352ed0190fe86587b53498457bf8c1024e51; original global index 16255.
def localCycle00147 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle d1f9a7ea6dc4672df44fb747e65cad456bf94d8105abcbc02e3ecc02d396dd65; original global index 16387.
def localCycle00148 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 21 0]

-- Original cycle d3b665fd249f507e3e2fac4628366ce4a6da943fc6d3ae50c0d8f4cbe990617e; original global index 16522.
def localCycle00149 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 32 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle d3f2c8e83327330af1ddca85f97a3683115b0d75b512b8c752f00afb573435d4; original global index 16543.
def localCycle00150 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 27 1, .triangle 26 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle d68861ad6b7f0125743e9e27376669fda648ad623ccb614b1c03342d6e0c4b06; original global index 16748.
def localCycle00151 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle d7a0ee3b8678425ee206219bd77250edae792c70e4f0432cd5ff60b83865eec7; original global index 16828.
def localCycle00152 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 2, .gapLower 0 5, .triangle 10 1, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle d92409a86dcb7e00390ad70eee88b2811c235bfc2e65c8e5038bcdbe96a437c7; original global index 16966.
def localCycle00153 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 33 1, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle d9fab7a50453f1b169432109e5371e495ba177bf12ef14a6cd99cc20be233fe4; original global index 17034.
def localCycle00154 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 3, .gapLower 3 2, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle da4be8ec76498f5a84c1e2072a5cb90c999887cf9e3baec64f9d352176721498; original global index 17053.
def localCycle00155 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle da970f717ad0d069fcf0fdea07aca78300a54722722ca633110af77d0fab16bb; original global index 17082.
def localCycle00156 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 3, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 26 1, .gapLower 3 2, .gapLower 0 3, .corridorLower 0 4, .thetaLower 0]

-- Original cycle e1d7f93ba70e7c49ff0ad562960d8501e99044f2cf65b3e52706c171a464e5f6; original global index 17660.
def localCycle00157 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 0, .triangle 33 1, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle e2f0c705c609eb2328bca722074275b9bdb45bcd93e5b55001afc6f44db43441; original global index 17750.
def localCycle00158 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 2, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .gapUpper 3 6, .thetaLower 3]

-- Original cycle e36ce5f10d7bebd815bd3dbbff95d9cdfa8846a891a22249051af374e6c6ec62; original global index 17786.
def localCycle00159 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle e703300fcf656c53726fd976dd7c55578a486451bd8c2d642276109971c6596a; original global index 18069.
def localCycle00160 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 26 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle e73827d5c71de82acfdec888be593e3468f4c3f6ff97ceaea5059bfc9942dfcd; original global index 18086.
def localCycle00161 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 6, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -2, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .gapLower 6 1, .triangle 11 1, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle e7d80fe7efdc9f38daf7b685c0ace0dbd4b2c129fed9ac882ae4469d6cf020ae; original global index 18130.
def localCycle00162 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapLower 6 2, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle ea0e5e18f119ba88a7f83db307d7ee0c2dd5ff4e2d44d07b466d25f5efe3a8a4; original global index 18286.
def localCycle00163 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle ecb0bea74ff5a126b59a94f32270b58f5c7c613d578d822fb098e66aeb2fe7fe; original global index 18478.
def localCycle00164 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 2 5, .distance 2 3, .distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 30 1, .triangle 26 1, .gapLower 3 2, .gapLower 0 3, .gapLower 4 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle ed0df6125f0b85ef8b8f758295f48b914290c0cee160ee5f46f610f1ff36639f; original global index 18506.
def localCycle00165 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 0, .gapLower 3 2, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle ef7ead2d718a771feaae886f27f78f751d5532fe4ffbff0dc9f3548161dc2487; original global index 18684.
def localCycle00166 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle efc36379099d78c93ed5d6e79b15f585869285f2d72ce326e7679d88667488b1; original global index 18702.
def localCycle00167 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 1 2, .triangle 9 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle f1ab325810f5d819229f538d1fca5f3f7be2f13399f03f7dedd4285c2be3df70; original global index 18843.
def localCycle00168 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .gapLower 3 2, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0]

-- Original cycle f2b38b0db659e2e100273505cca3713719f396eda7fe3617336e3ae5e7242bf3; original global index 18918.
def localCycle00169 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 5, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 10 1, .gapLower 0 3, .triangle 6 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle f420a4bdee4cbbd262625eeea031cc632190402bffb61770ca87138d474b0389; original global index 19037.
def localCycle00170 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 2, .triangle 18 0, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 5 2, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle f4bc8ff3d8d1c211d7571f81baaf788cf1f1c6437da67e27b2802cc2d7ced2d3; original global index 19077.
def localCycle00171 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .triangle 18 0, .triangle 15 0, .triangle 5 2, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle f4e5c1f7b0ed09c72e248c16518a148de25fe64538cf2ddfcd44e53328d8c8c2; original global index 19093.
def localCycle00172 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 0, .triangle 5 2, .triangle 9 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle f533118d4adf3a438592eb294ed88002e0e0feec1605956db729eee17ad4a63f; original global index 19115.
def localCycle00173 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle f5ae88baabd5ca91300c494bbc00851d3767a0a2200a5702a99519f94ea4794f; original global index 19161.
def localCycle00174 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -3, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 10 1, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle f5cb0d8f1edb652ccff7498deb0c8124cc1ec8f6365dbb9acaf38dcaa10d8bad; original global index 19176.
def localCycle00175 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle f7578b4b1237724388e3a4059d3b5fa04b4e003a463d3615f37466c6e16a8710; original global index 19294.
def localCycle00176 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 4]
    constant := ![2, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 23 1]

-- Original cycle f84613242d27743e6f9a991cfd2e922a4fb879341f41a7cbca8253c2196b3176; original global index 19362.
def localCycle00177 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 27 0, .gapLower 3 2, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle f88870c4c58f5ee75d3ffd20717270834dc4217cc78a005bd41eca6712296fcc; original global index 19382.
def localCycle00178 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 14 0, .gapLower 0 4, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle fd45c8e5e17d8d4cda7a29a74ad24151ab28eda859a8e6fb8b2e6b80ad0b2ef0; original global index 19794.
def localCycle00179 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0]
    constant := ![2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 10 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1]

-- Original cycle ffcdbe7aeded41e874016fa58b8c2ea9cacbe409394e364f6ef1cc8aa451d733; original global index 20009.
def localCycle00180 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

def library : Library := fun id => if id < 90 then (if id < 45 then (if id < 22 then (if id < 11 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 8 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none))) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none))))) else (if id < 16 then (if id < 13 then (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none)) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none)))) else (if id < 19 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none))) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)))))) else (if id < 33 then (if id < 27 then (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)))) else (if id < 30 then (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))))) else (if id < 39 then (if id < 36 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none))) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)))) else (if id < 42 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))))))) else (if id < 67 then (if id < 56 then (if id < 50 then (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)))) else (if id < 53 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none))) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none))))) else (if id < 61 then (if id < 58 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none)))) else (if id < 64 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)))))) else (if id < 78 then (if id < 72 then (if id < 69 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)))) else (if id < 75 then (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none))) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))))) else (if id < 84 then (if id < 81 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none))) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)))) else (if id < 87 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none))) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)))))))) else (if id < 135 then (if id < 112 then (if id < 101 then (if id < 95 then (if id < 92 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)))) else (if id < 98 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none))) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))))) else (if id < 106 then (if id < 103 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)))) else (if id < 109 then (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none))) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none)))))) else (if id < 123 then (if id < 117 then (if id < 114 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)))) else (if id < 120 then (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none))) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none))))) else (if id < 129 then (if id < 126 then (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none))) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)))) else (if id < 132 then (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none))) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none))))))) else (if id < 158 then (if id < 146 then (if id < 140 then (if id < 137 then (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)))) else (if id < 143 then (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none))) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none))))) else (if id < 152 then (if id < 149 then (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none))) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none)))) else (if id < 155 then (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none))) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none)))))) else (if id < 169 then (if id < 163 then (if id < 160 then (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none)) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none)))) else (if id < 166 then (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none))) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none))))) else (if id < 175 then (if id < 172 then (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id = 171 then some localCycle00171 else none))) else (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none)))) else (if id < 178 then (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none))) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 3, 6, 5], ![0, 4, 1, 6, 5, 3], ![4, 0, 1, 6, 5, 2], ![3, 0, 2, 1, 6, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 1, 3, 2, 4]], proof := .tail 13 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2304)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 6, 3, 5], ![0, 4, 1, 6, 5, 3], ![4, 0, 6, 1, 5, 2], ![3, 0, 2, 1, 6, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 1, 2, 4]], proof := .tail 29 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2305)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 6, 2, 3, 5], ![0, 4, 6, 1, 5, 3], ![4, 0, 6, 1, 5, 2], ![3, 0, 2, 1, 6, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 2, 1, 4]], proof := .tail 29 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2306)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 2, 3, 5], ![0, 4, 6, 1, 5, 3], ![4, 0, 6, 1, 5, 2], ![3, 0, 2, 6, 1, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 2, 4, 1]], proof := .tail 180 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2307)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 2, 3, 5], ![0, 6, 4, 1, 5, 3], ![4, 0, 6, 1, 5, 2], ![3, 0, 6, 2, 1, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 61 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2308)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 5, 3, 6], ![0, 4, 1, 5, 3, 6], ![4, 0, 5, 1, 2, 6], ![3, 0, 2, 1, 5, 6], ![0, 3, 1, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 85 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2309)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 5, 3, 6], ![0, 4, 1, 5, 3, 6], ![4, 0, 5, 1, 2, 6], ![3, 0, 2, 1, 6, 5], ![0, 3, 1, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 42 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2310)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 5, 3, 6], ![0, 4, 1, 5, 6, 3], ![4, 0, 5, 1, 6, 2], ![3, 0, 2, 1, 5, 6], ![0, 3, 1, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 43 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2311)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 5, 3, 6], ![0, 4, 1, 5, 6, 3], ![4, 0, 5, 1, 6, 2], ![3, 0, 2, 1, 6, 5], ![0, 3, 1, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 43 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2312)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 5, 3, 6], ![0, 4, 1, 6, 5, 3], ![4, 0, 5, 1, 6, 2], ![3, 0, 2, 1, 6, 5], ![0, 3, 1, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 46 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2313)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 5, 6, 3], ![0, 4, 1, 5, 6, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 2, 1, 5, 6], ![0, 3, 1, 2, 4, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 65 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2314)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 5, 6, 3], ![0, 4, 1, 5, 6, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 2, 1, 6, 5], ![0, 3, 1, 2, 6, 4], ![0, 3, 1, 2, 5, 4]], proof := .tail 98 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2315)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 5, 6, 3], ![0, 4, 1, 6, 5, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 2, 1, 6, 5], ![0, 3, 1, 6, 2, 4], ![0, 3, 1, 5, 2, 4]], proof := .tail 15 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2316)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 6, 5, 3], ![0, 4, 1, 6, 5, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 2, 1, 6, 5], ![0, 3, 6, 1, 2, 4], ![0, 3, 5, 1, 2, 4]], proof := .tail 117 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2317)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 6, 2, 5, 3], ![0, 4, 6, 1, 5, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 2, 1, 6, 5], ![0, 3, 6, 1, 2, 4], ![0, 3, 5, 2, 1, 4]], proof := .tail 125 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2318)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 2, 5, 3], ![0, 4, 6, 1, 5, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 2, 6, 1, 5], ![0, 3, 6, 1, 2, 4], ![0, 3, 5, 2, 4, 1]], proof := .tail 143 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2319)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 2, 5, 3], ![0, 6, 4, 1, 5, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 6, 2, 1, 5], ![0, 3, 6, 1, 2, 4], ![0, 3, 5, 4, 2, 1]], proof := .tail 101 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2320)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 6, 5, 3], ![0, 4, 1, 6, 5, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 2, 1, 6, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 3, 1, 2, 4]], proof := .tail 130 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2321)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 6, 2, 5, 3], ![0, 4, 6, 1, 5, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 2, 1, 6, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 3, 2, 1, 4]], proof := .tail 173 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2322)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 2, 5, 3], ![0, 4, 6, 1, 5, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 2, 6, 1, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 3, 2, 4, 1]], proof := .tail 49 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2323)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 2, 5, 3], ![0, 6, 4, 1, 5, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 6, 2, 1, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 109 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2324)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 5, 2, 3, 6], ![0, 4, 5, 1, 3, 6], ![4, 0, 5, 1, 2, 6], ![3, 0, 2, 1, 5, 6], ![0, 3, 2, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 111 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2325)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 5, 2, 3, 6], ![0, 4, 5, 1, 3, 6], ![4, 0, 5, 1, 2, 6], ![3, 0, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 114 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2326)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 5, 2, 3, 6], ![0, 4, 5, 1, 6, 3], ![4, 0, 5, 1, 6, 2], ![3, 0, 2, 1, 5, 6], ![0, 3, 2, 1, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 115 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2327)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 5, 2, 3, 6], ![0, 4, 5, 1, 6, 3], ![4, 0, 5, 1, 6, 2], ![3, 0, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 115 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2328)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 5, 2, 6, 3], ![0, 4, 5, 1, 6, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 2, 1, 5, 6], ![0, 3, 2, 1, 4, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 17 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2329)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 5, 2, 6, 3], ![0, 4, 5, 1, 6, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 4], ![0, 3, 1, 2, 5, 4]], proof := .tail 17 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2330)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 5, 6, 2, 3], ![0, 4, 5, 6, 1, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 2, 1, 5, 6], ![0, 3, 2, 1, 4, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 59 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2331)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 5, 6, 2, 3], ![0, 4, 5, 6, 1, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 4], ![0, 3, 2, 1, 5, 4]], proof := .tail 59 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2332)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 6, 5, 2, 3], ![0, 4, 5, 6, 1, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 2, 1, 6, 5], ![0, 3, 2, 6, 1, 4], ![0, 3, 2, 5, 1, 4]], proof := .tail 100 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2333)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 6, 5, 2, 3], ![0, 4, 6, 5, 1, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 2, 1, 6, 5], ![0, 3, 6, 2, 1, 4], ![0, 3, 5, 2, 1, 4]], proof := .tail 75 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2334)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 5, 2, 3], ![0, 4, 5, 6, 1, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 2, 6, 1, 5], ![0, 3, 2, 6, 1, 4], ![0, 3, 2, 5, 4, 1]], proof := .tail 8 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2335)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 5, 2, 3], ![0, 4, 6, 5, 1, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 2, 6, 1, 5], ![0, 3, 6, 2, 1, 4], ![0, 3, 5, 2, 4, 1]], proof := .tail 75 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2336)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 1, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 6, 2, 1, 5], ![0, 3, 6, 2, 1, 4], ![0, 3, 5, 4, 2, 1]], proof := .tail 119 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2337)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 6, 5, 2, 3], ![0, 4, 6, 5, 1, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 2, 1, 6, 5], ![0, 6, 3, 2, 1, 4], ![0, 5, 3, 2, 1, 4]], proof := .tail 95 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2338)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 5, 2, 3], ![0, 4, 6, 5, 1, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 2, 6, 1, 5], ![0, 6, 3, 2, 1, 4], ![0, 5, 3, 2, 4, 1]], proof := .tail 95 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2339)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 1, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 6, 2, 1, 5], ![0, 6, 3, 2, 1, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 66 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2340)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 4, 2, 3, 6], ![0, 4, 5, 1, 3, 6], ![4, 0, 5, 1, 2, 6], ![3, 0, 2, 5, 1, 6], ![0, 3, 2, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 36 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2341)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 4, 2, 3, 6], ![0, 4, 5, 1, 6, 3], ![4, 0, 5, 1, 6, 2], ![3, 0, 2, 5, 1, 6], ![0, 3, 2, 4, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 1 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2342)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 4, 2, 6, 3], ![0, 4, 5, 1, 6, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 2, 5, 1, 6], ![0, 3, 2, 4, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 56 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2343)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 4, 6, 2, 3], ![0, 4, 5, 6, 1, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 2, 5, 1, 6], ![0, 3, 2, 4, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 2 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2344)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 6, 4, 2, 3], ![0, 4, 5, 6, 1, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 2, 5, 6, 1], ![0, 3, 2, 4, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 86 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2345)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 4, 5, 6, 1, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 2, 5, 6, 1], ![0, 3, 2, 4, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 105 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2346)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 4, 5, 6, 1, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 2, 6, 5, 1], ![0, 3, 2, 6, 4, 1], ![0, 3, 2, 5, 4, 1]], proof := .tail 6 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2347)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 4, 6, 5, 1, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 2, 6, 5, 1], ![0, 3, 6, 2, 4, 1], ![0, 3, 5, 2, 4, 1]], proof := .tail 139 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2348)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 4, 5, 1, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 6, 2, 5, 1], ![0, 3, 6, 2, 4, 1], ![0, 3, 5, 4, 2, 1]], proof := .tail 92 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2349)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 4, 6, 5, 1, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 2, 6, 5, 1], ![0, 6, 3, 2, 4, 1], ![0, 5, 3, 2, 4, 1]], proof := .tail 88 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2350)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 4, 5, 1, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 6, 2, 5, 1], ![0, 6, 3, 2, 4, 1], ![0, 5, 3, 4, 2, 1]], proof := .tail 92 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2351)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 4, 2, 3, 6], ![0, 5, 4, 1, 3, 6], ![4, 0, 5, 1, 2, 6], ![3, 0, 5, 2, 1, 6], ![0, 3, 4, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 10 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2352)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 4, 2, 3, 6], ![0, 5, 4, 1, 6, 3], ![4, 0, 5, 1, 6, 2], ![3, 0, 5, 2, 1, 6], ![0, 3, 4, 2, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 136 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2353)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 4, 2, 6, 3], ![0, 5, 4, 1, 6, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 5, 2, 1, 6], ![0, 3, 4, 2, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 9 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2354)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 4, 6, 2, 3], ![0, 5, 4, 6, 1, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 5, 2, 1, 6], ![0, 3, 4, 2, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 166 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2355)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 6, 4, 2, 3], ![0, 5, 4, 6, 1, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 5, 2, 6, 1], ![0, 3, 4, 2, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 14 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2356)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 5, 6, 2, 1], ![0, 3, 4, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 82 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2357)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 5, 4, 6, 1, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 5, 2, 6, 1], ![0, 3, 4, 2, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 155 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2358)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 5, 6, 2, 1], ![0, 3, 4, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 50 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2359)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 5, 6, 2, 1], ![0, 3, 4, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 25 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2360)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 6, 5, 2, 1], ![0, 3, 6, 4, 2, 1], ![0, 3, 5, 4, 2, 1]], proof := .tail 32 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2361)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 6, 5, 2, 1], ![0, 6, 3, 4, 2, 1], ![0, 5, 3, 4, 2, 1]], proof := .tail 18 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2362)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 3, 2, 5, 6], ![0, 4, 3, 1, 5, 6], ![4, 0, 2, 1, 5, 6], ![3, 0, 2, 1, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 63 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2363)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 3, 2, 5, 6], ![0, 4, 3, 1, 5, 6], ![4, 0, 2, 1, 5, 6], ![3, 0, 2, 1, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 48 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2364)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 3, 2, 5, 6], ![0, 4, 3, 1, 5, 6], ![4, 0, 2, 1, 6, 5], ![3, 0, 2, 1, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 31 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2365)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 3, 2, 5, 6], ![0, 4, 3, 1, 6, 5], ![4, 0, 2, 1, 6, 5], ![3, 0, 2, 1, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 99 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2366)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 3, 2, 6, 5], ![0, 4, 3, 1, 6, 5], ![4, 0, 2, 1, 6, 5], ![3, 0, 2, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .low6 (![96, 122, 16, 138, 3, 148, 171, 79, 4, 147, 64, 89, 123, 37, 55, 64, 89, 141, 74, 64, 89, 162, 87, 176, 127, 104, 64, 89]) }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2367)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 3, 6, 2, 5], ![0, 4, 3, 6, 1, 5], ![4, 0, 2, 1, 6, 5], ![3, 0, 2, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 128 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2368)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 6, 3, 2, 5], ![0, 4, 3, 6, 1, 5], ![4, 0, 2, 6, 1, 5], ![3, 0, 2, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 3, 1, 4]], proof := .tail 77 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2369)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 6, 3, 2, 5], ![0, 4, 6, 3, 1, 5], ![4, 0, 6, 2, 1, 5], ![3, 0, 2, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 2, 1, 4]], proof := .tail 73 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2370)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 3, 2, 5], ![0, 4, 3, 6, 1, 5], ![4, 0, 2, 6, 1, 5], ![3, 0, 2, 6, 1, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 3, 4, 1]], proof := .tail 126 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2371)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 3, 2, 5], ![0, 4, 6, 3, 1, 5], ![4, 0, 6, 2, 1, 5], ![3, 0, 2, 6, 1, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 2, 4, 1]], proof := .tail 73 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2372)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 1, 5], ![4, 0, 6, 2, 1, 5], ![3, 0, 6, 2, 1, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 137 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2373)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 3, 5, 2, 6], ![0, 4, 3, 5, 1, 6], ![4, 0, 2, 1, 5, 6], ![3, 0, 2, 1, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .low0 (![175, 120, 39, 133, 145, 174, 80, 71, 45, 132, 107, 90, 90, 30, 71, 71, 71, 71, 168, 94, 94, 54, 67, 169, 24, 34, 33, 23]) }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2374)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 3, 5, 2, 6], ![0, 4, 3, 5, 1, 6], ![4, 0, 2, 1, 5, 6], ![3, 0, 2, 1, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 83 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2375)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 3, 5, 2, 6], ![0, 4, 3, 5, 1, 6], ![4, 0, 2, 1, 6, 5], ![3, 0, 2, 1, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 11 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2376)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 3, 5, 6, 2], ![0, 4, 3, 5, 6, 1], ![4, 0, 2, 1, 5, 6], ![3, 0, 2, 1, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .low6 (![112, 62, 131, 124, 44, 47, 118, 22, 28, 146, 113, 76, 26, 93, 161, 161, 161, 161, 97, 91, 51, 57, 38, 149, 60, 20, 158, 140]) }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2377)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 3, 5, 6, 2], ![0, 4, 3, 5, 6, 1], ![4, 0, 2, 1, 5, 6], ![3, 0, 2, 1, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 167 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2378)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 3, 5, 6, 2], ![0, 4, 3, 5, 6, 1], ![4, 0, 2, 1, 6, 5], ![3, 0, 2, 1, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 2, 1, 5, 3, 4]], proof := .low0 (![108, 120, 39, 133, 144, 129, 80, 71, 94, 68, 178, 152, 35, 30, 71, 71, 71, 71, 19, 94, 94, 94, 110, 164, 156, 72, 58, 179]) }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2379)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 3, 6, 5, 2], ![0, 4, 3, 5, 6, 1], ![4, 0, 2, 1, 6, 5], ![3, 0, 2, 1, 6, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 1, 3, 4]], proof := .tail 21 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2380)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 3, 6, 5, 2], ![0, 4, 3, 6, 5, 1], ![4, 0, 2, 1, 6, 5], ![3, 0, 2, 1, 6, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 41 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2381)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 6, 3, 5, 2], ![0, 4, 3, 5, 6, 1], ![4, 0, 2, 6, 1, 5], ![3, 0, 2, 1, 6, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 3, 1, 4]], proof := .tail 172 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2382)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 6, 3, 5, 2], ![0, 4, 3, 6, 5, 1], ![4, 0, 2, 6, 1, 5], ![3, 0, 2, 1, 6, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 3, 1, 4]], proof := .tail 41 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2383)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 6, 3, 5, 2], ![0, 4, 6, 3, 5, 1], ![4, 0, 6, 2, 1, 5], ![3, 0, 2, 1, 6, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 3, 2, 1, 4]], proof := .tail 106 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2384)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 3, 5, 2], ![0, 4, 3, 5, 6, 1], ![4, 0, 2, 6, 1, 5], ![3, 0, 2, 6, 1, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 3, 4, 1]], proof := .tail 177 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2385)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 3, 5, 2], ![0, 4, 3, 6, 5, 1], ![4, 0, 2, 6, 1, 5], ![3, 0, 2, 6, 1, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 3, 4, 1]], proof := .tail 41 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2386)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 3, 5, 2], ![0, 4, 6, 3, 5, 1], ![4, 0, 6, 2, 1, 5], ![3, 0, 2, 6, 1, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 3, 2, 4, 1]], proof := .tail 106 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2387)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 1], ![4, 0, 6, 2, 1, 5], ![3, 0, 6, 2, 1, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 70 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2388)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 5, 3, 2, 6], ![0, 4, 3, 5, 1, 6], ![4, 0, 2, 5, 1, 6], ![3, 0, 2, 1, 5, 6], ![0, 2, 3, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 102 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2389)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 5, 3, 2, 6], ![0, 4, 3, 5, 1, 6], ![4, 0, 2, 5, 1, 6], ![3, 0, 2, 1, 6, 5], ![0, 2, 3, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 170 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2390)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 5, 3, 6, 2], ![0, 4, 3, 5, 6, 1], ![4, 0, 2, 5, 1, 6], ![3, 0, 2, 1, 5, 6], ![0, 2, 3, 1, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 102 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2391)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 5, 3, 6, 2], ![0, 4, 3, 5, 6, 1], ![4, 0, 2, 5, 1, 6], ![3, 0, 2, 1, 6, 5], ![0, 2, 3, 1, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 69 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2392)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 5, 6, 3, 2], ![0, 4, 3, 5, 6, 1], ![4, 0, 2, 5, 6, 1], ![3, 0, 2, 1, 5, 6], ![0, 2, 3, 1, 4, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 142 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2393)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 5, 6, 3, 2], ![0, 4, 3, 5, 6, 1], ![4, 0, 2, 5, 6, 1], ![3, 0, 2, 1, 6, 5], ![0, 2, 3, 1, 6, 4], ![0, 2, 3, 1, 5, 4]], proof := .tail 165 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2394)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 6, 5, 3, 2], ![0, 4, 3, 5, 6, 1], ![4, 0, 2, 5, 6, 1], ![3, 0, 2, 1, 6, 5], ![0, 2, 3, 6, 1, 4], ![0, 2, 3, 5, 1, 4]], proof := .tail 52 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2395)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 6, 5, 3, 2], ![0, 4, 3, 5, 6, 1], ![4, 0, 2, 6, 5, 1], ![3, 0, 2, 1, 6, 5], ![0, 2, 6, 3, 1, 4], ![0, 2, 5, 3, 1, 4]], proof := .tail 78 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2396)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 6, 5, 3, 2], ![0, 4, 3, 6, 5, 1], ![4, 0, 2, 6, 5, 1], ![3, 0, 2, 1, 6, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 2, 3, 1, 4]], proof := .tail 135 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2397)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 6, 5, 3, 2], ![0, 4, 6, 3, 5, 1], ![4, 0, 6, 2, 5, 1], ![3, 0, 2, 1, 6, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 3, 2, 1, 4]], proof := .tail 7 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2398)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 4, 3, 5, 6, 1], ![4, 0, 2, 5, 6, 1], ![3, 0, 2, 6, 1, 5], ![0, 2, 3, 6, 1, 4], ![0, 2, 3, 5, 4, 1]], proof := .tail 5 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2399)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 4, 3, 5, 6, 1], ![4, 0, 2, 6, 5, 1], ![3, 0, 2, 6, 1, 5], ![0, 2, 6, 3, 1, 4], ![0, 2, 5, 3, 4, 1]], proof := .tail 78 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2400)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 4, 3, 6, 5, 1], ![4, 0, 2, 6, 5, 1], ![3, 0, 2, 6, 1, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 2, 3, 4, 1]], proof := .tail 135 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2401)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 4, 6, 3, 5, 1], ![4, 0, 6, 2, 5, 1], ![3, 0, 2, 6, 1, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 3, 2, 4, 1]], proof := .tail 7 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2402)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 3, 5, 1], ![4, 0, 6, 2, 5, 1], ![3, 0, 6, 2, 1, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 7 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2403)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 5, 3, 2, 6], ![0, 4, 5, 3, 1, 6], ![4, 0, 5, 2, 1, 6], ![3, 0, 2, 1, 5, 6], ![0, 3, 2, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 103 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2404)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 5, 3, 2, 6], ![0, 4, 5, 3, 1, 6], ![4, 0, 5, 2, 1, 6], ![3, 0, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 160 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2405)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 5, 3, 6, 2], ![0, 4, 5, 3, 6, 1], ![4, 0, 5, 2, 1, 6], ![3, 0, 2, 1, 5, 6], ![0, 3, 2, 1, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 150 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2406)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 5, 3, 6, 2], ![0, 4, 5, 3, 6, 1], ![4, 0, 5, 2, 1, 6], ![3, 0, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 150 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2407)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 5, 6, 3, 2], ![0, 4, 5, 3, 6, 1], ![4, 0, 5, 2, 6, 1], ![3, 0, 2, 1, 5, 6], ![0, 3, 2, 1, 4, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 116 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2408)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 5, 6, 3, 2], ![0, 4, 5, 3, 6, 1], ![4, 0, 5, 2, 6, 1], ![3, 0, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 4], ![0, 2, 3, 1, 5, 4]], proof := .tail 116 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2409)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 6, 5, 3, 2], ![0, 4, 5, 3, 6, 1], ![4, 0, 5, 2, 6, 1], ![3, 0, 2, 1, 6, 5], ![0, 3, 2, 6, 1, 4], ![0, 2, 3, 5, 1, 4]], proof := .tail 53 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2410)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 5, 6, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 0, 5, 6, 2, 1], ![3, 0, 2, 1, 5, 6], ![0, 3, 2, 1, 4, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 157 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2411)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 5, 6, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 0, 5, 6, 2, 1], ![3, 0, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 4], ![0, 3, 2, 1, 5, 4]], proof := .tail 157 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2412)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 6, 5, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 0, 5, 6, 2, 1], ![3, 0, 2, 1, 6, 5], ![0, 3, 2, 6, 1, 4], ![0, 3, 2, 5, 1, 4]], proof := .tail 52 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2413)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 0, 5, 6, 2, 1], ![3, 0, 2, 1, 6, 5], ![0, 3, 6, 2, 1, 4], ![0, 3, 5, 2, 1, 4]], proof := .tail 163 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2414)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 0, 6, 5, 2, 1], ![3, 0, 2, 1, 6, 5], ![0, 6, 3, 2, 1, 4], ![0, 5, 3, 2, 1, 4]], proof := .tail 121 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2415)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 4, 5, 3, 6, 1], ![4, 0, 5, 2, 6, 1], ![3, 0, 2, 6, 1, 5], ![0, 3, 2, 6, 1, 4], ![0, 2, 3, 5, 4, 1]], proof := .tail 134 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2416)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 0, 5, 6, 2, 1], ![3, 0, 2, 6, 1, 5], ![0, 3, 2, 6, 1, 4], ![0, 3, 2, 5, 4, 1]], proof := .tail 5 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2417)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 0, 5, 6, 2, 1], ![3, 0, 2, 6, 1, 5], ![0, 3, 6, 2, 1, 4], ![0, 3, 5, 2, 4, 1]], proof := .tail 163 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2418)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 0, 6, 5, 2, 1], ![3, 0, 2, 6, 1, 5], ![0, 6, 3, 2, 1, 4], ![0, 5, 3, 2, 4, 1]], proof := .tail 12 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2419)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 0, 5, 6, 2, 1], ![3, 0, 6, 2, 1, 5], ![0, 3, 6, 2, 1, 4], ![0, 3, 5, 4, 2, 1]], proof := .tail 40 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2420)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 0, 6, 5, 2, 1], ![3, 0, 6, 2, 1, 5], ![0, 6, 3, 2, 1, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 121 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2421)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 4, 3, 2, 6], ![0, 4, 3, 5, 1, 6], ![4, 0, 2, 5, 1, 6], ![3, 0, 2, 5, 1, 6], ![0, 2, 3, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 151 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2422)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 4, 3, 6, 2], ![0, 4, 3, 5, 6, 1], ![4, 0, 2, 5, 1, 6], ![3, 0, 2, 5, 1, 6], ![0, 2, 3, 4, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 151 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2423)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 4, 6, 3, 2], ![0, 4, 3, 5, 6, 1], ![4, 0, 2, 5, 6, 1], ![3, 0, 2, 5, 1, 6], ![0, 2, 3, 4, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 151 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2424)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 4, 3, 5, 6, 1], ![4, 0, 2, 5, 6, 1], ![3, 0, 2, 5, 6, 1], ![0, 2, 3, 4, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 153 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2425)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 3, 5, 6, 1], ![4, 0, 2, 5, 6, 1], ![3, 0, 2, 5, 6, 1], ![0, 2, 3, 4, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 27 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2426)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 3, 5, 6, 1], ![4, 0, 2, 5, 6, 1], ![3, 0, 2, 6, 5, 1], ![0, 2, 3, 6, 4, 1], ![0, 2, 3, 5, 4, 1]], proof := .tail 81 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2427)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 3, 5, 6, 1], ![4, 0, 2, 6, 5, 1], ![3, 0, 2, 6, 5, 1], ![0, 2, 6, 3, 4, 1], ![0, 2, 5, 3, 4, 1]], proof := .tail 154 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2428)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 3, 6, 5, 1], ![4, 0, 2, 6, 5, 1], ![3, 0, 2, 6, 5, 1], ![0, 6, 2, 3, 4, 1], ![0, 5, 2, 3, 4, 1]], proof := .tail 0 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2429)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 6, 3, 5, 1], ![4, 0, 6, 2, 5, 1], ![3, 0, 2, 6, 5, 1], ![0, 6, 2, 3, 4, 1], ![0, 5, 3, 2, 4, 1]], proof := .tail 159 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2430)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 3, 5, 1], ![4, 0, 6, 2, 5, 1], ![3, 0, 6, 2, 5, 1], ![0, 6, 2, 3, 4, 1], ![0, 5, 3, 4, 2, 1]], proof := .tail 84 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2431)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (2304 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 2304 ≤ id.val) (hhigh : id.val < 2432) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 2304)) = true := by
  let j : Fin 128 := ⟨id.val - 2304, by omega⟩
  have hsum : 2304 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (2304 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard018
