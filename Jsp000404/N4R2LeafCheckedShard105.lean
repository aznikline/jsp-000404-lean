import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard105
open N4R2RowDataReplay

-- Original cycle 00136ca500f417d58cb072db336ed0235f5d89e79c188b539eb5828d7fcb0e3f; original global index 9.
def localCycle00000 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 22 1, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 0042e2323538d857a5d482851e3247334063026b191b7d00b1bb4c386167f473; original global index 24.
def localCycle00001 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 2, .triangle 13 1, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 016fa4a26b855615b0c9caf6be53a1137ec1d7d3e24a44bf23a8020818830236; original global index 117.
def localCycle00002 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .gapLower 0 4, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 017fed1786d94671dad537be8b3b02ddd22dbb0a0ce35999b262417461c5832a; original global index 125.
def localCycle00003 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -3, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 6 3, .triangle 13 1, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 04e0f8711aa482fdd36051ca7396fc00ce0403a790130c300875a755c63546c2; original global index 393.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 2 6, .distance 1 6, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 18 2, .triangle 23 1, .triangle 13 0, .triangle 2 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 0660da827a856081780313a07e5cf60ef0bc95a25b82711ff950d0b4846a76d1; original global index 523.
def localCycle00005 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 18 2, .gapLower 6 3, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 06ae72ea9386ed884a86d3c50ba7ddb1ecc2e4a65de0e73ab02a7f18ab757920; original global index 550.
def localCycle00006 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 0 1]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 0 2, .gapUpper 2 2, .gapLower 6 5, .triangle 4 0]

-- Original cycle 07e07c900646a2bc8a3d0495af20dff46f0b701dae8bae333cd309f87a74bf48; original global index 636.
def localCycle00007 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 097ac2ac85f77c583742b1fd64d52a8a6ad4de8fdc6299e75e646c4c01c8a7b5; original global index 753.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .triangle 22 1, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 0ae84a71318bab0ac70e10ea68488e5e1da7ed6d896a10f48506b2bca381269d; original global index 872.
def localCycle00009 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 0, .triangle 3 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 0c18dd231bd230e1d0bb893a54368de04bb93c69f4374b93e2dd1b528d353bb3; original global index 955.
def localCycle00010 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 3 5, .distance 3 6, .distance 5 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 10 0, .triangle 33 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 0c6f60d9f5dec444cd4e204ba25f4695c03f266c7ed0a243aa6e57af8c3fe150; original global index 984.
def localCycle00011 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 3, .gapUpper 5 3]

-- Original cycle 0c75e68b568a4a7572d16e379e1bb120b5dd72b1536929176d128fc9613a9912; original global index 986.
def localCycle00012 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 8 2, .triangle 13 1, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 0c838359747cc77e3aadd3b7846e254946624c58fba75144b49a4c3ae5f85fc3; original global index 991.
def localCycle00013 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 4 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 18 2, .triangle 23 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 0cca73e0c4a0dd7decac0ae922a69a1babfe0f5040da8cb2200767116d003384; original global index 1011.
def localCycle00014 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 3 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 23 0, .triangle 32 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 0d592430b92c91e61f2ba0fe082b3ea4b6500c961dbf2ebca825f167f84708b7; original global index 1057.
def localCycle00015 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 17 2, .triangle 3 2, .triangle 14 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 0ea29633a3a2fd0bba1905c215b049014d2ee17610df510cbf4a3481ef5f7ab7; original global index 1156.
def localCycle00016 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 2 6, .distance 2 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 29 1]

-- Original cycle 10972a112647bcb06ddcf496032dc6824956499f702c85863591391ac83d77dc; original global index 1331.
def localCycle00017 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 12 0, .triangle 2 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 11895c49aead325241f7cea7f70c38d2aa654fe186198ae03192f3efaf3b761c; original global index 1399.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .gapLower 6 3, .triangle 32 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 11aa3970052fecd2cc18f884756e1b6c7ca4eb41d7557c9bd835b2e7c6423c9b; original global index 1411.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, 0, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 10 2, .triangle 14 2, .gapLower 6 2, .triangle 32 1, .corridorLower 3 4]

-- Original cycle 11ecded0725b9da2d9c8731077336562c3edb1107ac490b7eb28358a6386a079; original global index 1434.
def localCycle00020 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 4 6, .distance 5 6, .distance 3 5, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 18 2, .triangle 23 1, .triangle 34 1, .triangle 33 0, .gapLower 5 0]

-- Original cycle 126e643e8e2e01762c853f372146ff5f6f9bb6f682ad2843e26499a320681beb; original global index 1463.
def localCycle00021 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .gapLower 6 2, .gapLower 6 1, .triangle 32 1, .corridorLower 3 4]

-- Original cycle 137cd2bf425e0c3b987b4670d2f6a7a0477b4708d83a451a1963a35560408913; original global index 1536.
def localCycle00022 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 13b1f51d30eac8904a796ede7be6dbbc29afc2740d79b5dd6725e1cbd4dfcf80; original global index 1557.
def localCycle00023 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 3, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 13bd2926a6254b327cba55c14aee1181a683cf7fc644a7e8c46c127c1f75ddff; original global index 1564.
def localCycle00024 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 3 5, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 0, .triangle 31 2, .triangle 33 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 161e2aeefaa754f896ab843e325eb1017f047b143d7480788b0cbd91d852cb7b; original global index 1748.
def localCycle00025 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle 16d62e49f7dc19ba05846782bde2a39b4b2553d82ef137363eb96062dfa11c68; original global index 1794.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 17225da60a18f45b4f7199a4fc6db54f8c0902b8a1dc639fdd387188f30c24c8; original global index 1817.
def localCycle00027 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![4, -1, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 5 6, .triangle 12 0, .triangle 13 0, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 178dcb6b18f97e1460b479aace01ad78adcc0564edbe61b07d1ebe64c81f2af8; original global index 1841.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 1 6, .distance 5 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 18 2, .triangle 24 1, .triangle 33 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 18e6c24319b2e858f4c2268a2ca7394eeeede6d92d94c12f78e52c36ba8a70ec; original global index 1945.
def localCycle00029 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 1cddd4efb1238ffef8d328938a3034044357124c35b45daa04da9ab7c9d462b3; original global index 2220.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 18 2, .triangle 23 1, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 1dba537e1e900a4624e8dd159491066aaa764dc401b67dffb4424cceaa43ef4a; original global index 2286.
def localCycle00031 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .triangle 14 2, .triangle 11 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 1e0a395ec9b56a324be2f4cb07b2ca9baf2077bbd99b3ae6f231e945b76919e1; original global index 2310.
def localCycle00032 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 3 5, .distance 3 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 0, .triangle 31 2, .triangle 33 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 1e32c4cde819ea6014dcaaa1719f48510801e8447b3321d35087d1b0053ab20a; original global index 2324.
def localCycle00033 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 12 0, .triangle 2 1, .triangle 0 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 1e818425906da48f2d2597dbe9c1f2816b41ad65b1f849e43f75d24a37525267; original global index 2343.
def localCycle00034 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 0, .triangle 12 0, .triangle 2 1, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 1f1d2cea5969ab9418fdacc5ff1fdbdffbf8971599d7f2755b20a5857be38d94; original global index 2388.
def localCycle00035 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 0, .triangle 17 2, .triangle 3 0, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 1fe1402272391aa69f907c5c54bbe816026f25402348f67765f8e639f6f932e0; original global index 2448.
def localCycle00036 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -2, -2, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 6 3, .gapLower 6 2, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle 1ffca571c34ce8e54e43be7d1ebb818cba0fde87d8844848dc981aa779727f3d; original global index 2454.
def localCycle00037 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 4 5, .distance 3 5, .distance 0 3]
    constant := ![-3, 0, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 4, .gapLower 4 2, .gapLower 5 1, .gapUpper 3 2]

-- Original cycle 210494c3bc1db1ecf30e558cc4aa5f3e4c8f5fec3a157a4383c4e0fa9e2f4eb9; original global index 2533.
def localCycle00038 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 13 1, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 213a497cf476fbb8491ff7e519abf60defce82eb604902671df0e901819fad8e; original global index 2547.
def localCycle00039 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapLower 6 3, .triangle 14 0, .triangle 12 1, .triangle 2 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 217a0f61d52c3f896343f31e37cb1da1a7013a700049c8156dd517450dbf7de7; original global index 2563.
def localCycle00040 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 222da5d54c8104705a6b1dcb7b363641ae1c0e9d3139bf0ed3620a3f2582739c; original global index 2618.
def localCycle00041 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 3, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 249631f3ed9b69801ea3e8f2687d6defbf85080bf1349e69bc11e2683edc2fa5; original global index 2808.
def localCycle00042 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 3 6, .theta 6]
    constant := ![3, -2, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 8 2, .triangle 13 1, .triangle 32 2, .gapLower 6 0]

-- Original cycle 25c2d9b0909755e4ddbb071448896f61b7fef27fbc1bb0d0b9770b9648d229a4; original global index 2901.
def localCycle00043 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 5, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 0, .triangle 22 1, .triangle 12 0, .triangle 2 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 28eaf90736c0d3484635e83fa244e4a1cebe74263461ed4c6bf3dacabfb475a5; original global index 3129.
def localCycle00044 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 2 5, .triangle 17 2, .triangle 24 2, .gapLower 6 4, .triangle 13 1, .triangle 32 2, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 29381b59ec0d0ff15bc638690841fce5172d4e2b1194df364adacd447312ec4e; original global index 3144.
def localCycle00045 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 22 0, .triangle 2 0, .triangle 4 0, .triangle 21 1, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 298ec2dad45665bd56e18f3386a751d8f782e941290493b50c509887f1148346; original global index 3170.
def localCycle00046 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 2 4]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 2 3, .gapUpper 5 5, .gapLower 6 5, .triangle 29 0]

-- Original cycle 2a8029e8a3eb6c9a1ec2df30dba38ea76f23edb643c0de506ba4b877bb39f0a9; original global index 3238.
def localCycle00047 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 4 6, .distance 0 4, .distance 0 1]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 1 2, .gapLower 6 4, .triangle 13 0, .triangle 2 1]

-- Original cycle 2b0e183e761210dfee6086a5f3c09898551980200518e65b8992655820a7f34e; original global index 3287.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .gapLower 6 3, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 2b63977b8747468727b1ccf18242b440a28026761565de184fda1b3de92021e5; original global index 3320.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .distance 3 5, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 13 1, .triangle 34 1, .triangle 33 0, .gapLower 5 0]

-- Original cycle 2c625ee2923301fefdaccabb597bc80c28b5250edf9c40fc182c4c707b9056a5; original global index 3393.
def localCycle00050 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 11 1, .triangle 32 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 2d2f5bae0da87bc3cdd3b0d9a3b864cce1b1aa0ff14e92a3cfe257e16841a911; original global index 3450.
def localCycle00051 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -3, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 6 3, .triangle 4 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 2d3ac9a4026ffa017a19e38d482972c7ce01b8014b6922c7f563da9c8652d037; original global index 3452.
def localCycle00052 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Original cycle 2e7b3b3bc633d7057316a2420cc38129f26f16a1dec6d0b929fe2e1713aa139b; original global index 3554.
def localCycle00053 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -2, 0, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 18 2, .triangle 23 1, .triangle 34 1, .triangle 12 0, .triangle 2 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 2f6095b14b9e5c70a1d00376d82dd65d454a029e11fb6f1c14f80ba2f7d9b43d; original global index 3620.
def localCycle00054 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 0, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 30c4ffcd4659527af7f5acf751485dc13fe7ad9fc6e7063ec5ca85c07f098719; original global index 3717.
def localCycle00055 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 3 6, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 1, .gapLower 6 2, .triangle 32 1]

-- Original cycle 30c5f2d4c1e3b63a57c9cd1893f13f4fe7d40811b6d3647b08984e7952181521; original global index 3719.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .gapLower 6 2, .triangle 11 1, .triangle 32 1, .corridorLower 3 4]

-- Original cycle 3135113c390d6fc0da03505a5e96831eaf57976e48e32246fb93a4ff14dcf941; original global index 3751.
def localCycle00057 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .triangle 11 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 313a97b5422fbbe0eb05dd908aeadde8925c9165be1c8700f182637e811045da; original global index 3756.
def localCycle00058 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 6 3, .gapLower 6 2, .triangle 11 1, .triangle 32 1, .corridorLower 3 4]

-- Original cycle 32a1fcaab3e001f1588b40b2811fa46c7547b0c12024a91b9e91d58c261abe4a; original global index 3874.
def localCycle00059 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .distance 3 5, .distance 0 3]
    constant := ![-2, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 4, .gapLower 0 3, .gapLower 5 2, .triangle 31 2, .gapUpper 3 2]

-- Original cycle 32aee239d0a3a840ae1bd5f502be22b087073092f5a97cdc443e4934f49cee1e; original global index 3878.
def localCycle00060 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 12 0, .triangle 9 1, .corridorLower 3 4]

-- Original cycle 32bb582b08af208d1cf407c001c72271ca3dd196e41ea954a975dcf33e8b0091; original global index 3885.
def localCycle00061 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 331d508e181faabf8c3cfd8118afcefa0d9c7048f61cc16d628f67108ade09bc; original global index 3911.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 9 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 336444b177d326701cb39cd17593b4ed69028866adcb6b3a6705f39f0db266bf; original global index 3935.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, 0, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .triangle 18 2, .triangle 4 2, .gapLower 6 3, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 34d563f54cd7b8d131e88e97a07c6dd43b0f44baafeacdadbecf89bb8e5cdc6a; original global index 4041.
def localCycle00064 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0, .triangle 23 1, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 35304026d1e8f4cea04189770a9825e4eec0bb9973db95c200848b487a60d79d; original global index 4069.
def localCycle00065 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .triangle 22 1, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 35853cc4a281dbe82f909da7dff06a45009215052b77961277bf994f55c85a7b; original global index 4099.
def localCycle00066 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 22 0, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 36aa4fd5a65e4578f81cff6ccdfc5f40abf18416e035e12e2a749592e3090fb4; original global index 4200.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0, .triangle 24 1, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 36e133be40c8fe412ffeec767bcf5b2e3b18ee8d526b02403bf76b1fb78be052; original global index 4214.
def localCycle00068 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -2, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 2, .gapLower 6 3, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 371628b669aedcbb3ed1807fd63d75041a5c2707af3ac4597b2b05db40fb3a53; original global index 4227.
def localCycle00069 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 8 2, .gapLower 6 1, .corridorLower 3 6, .thetaLower 3]

-- Original cycle 375f1199e24cfe81523fa5b667a63a159d1c0c9229a4c53061ee3e101881426f; original global index 4254.
def localCycle00070 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 1 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -3, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .triangle 23 1, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 383fefa1491b9682e929f62364783f457a9d912d031cef1501bc9fa251da447d; original global index 4317.
def localCycle00071 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 18 2, .triangle 4 0, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 3848c3c4e5adfa8d575cf0cb19bac02f71af2088c072a127b2707e8177773bca; original global index 4321.
def localCycle00072 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 8 2, .gapLower 6 3, .triangle 32 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 38c8984db6f7629b21de6845d86858f8edc96c721a5b4a25405dd2fda4a84de6; original global index 4370.
def localCycle00073 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 3ae2f6c888cd550fe3c62544da86273de6c97e40b806735a1e32907b054bcf67; original global index 4546.
def localCycle00074 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 2, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 3bd49413d344059fb2b526fb9e20b9f94a11415b75dff25ede05fec11c71597b; original global index 4630.
def localCycle00075 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 0 6, .distance 3 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 23 2, .triangle 4 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 3bd69763bc37fcc323d431f2ebc8a7f33e277ee33dacbf4ef574de575f21775d; original global index 4633.
def localCycle00076 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 3 5, .theta 5]
    constant := ![3, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 4 2, .triangle 14 1, .triangle 33 0, .gapLower 5 0]

-- Original cycle 3cd59373c4f90c3b012b0ee246dcab20c9b17ed7463e6eebc75adad6814c284c; original global index 4717.
def localCycle00077 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 5 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 17 2, .triangle 3 2, .triangle 14 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 3d0611dce37c6a87abe1d39b6bffe4a722580ec4f429c6ed2c2b84e6bc04db85; original global index 4725.
def localCycle00078 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 3d9201047a9601a34bb78a4f33051731afe0b505f0730b820c1acc859f4d9d2c; original global index 4766.
def localCycle00079 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 4 6, .distance 2 6, .distance 2 5]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 30 1]

-- Original cycle 3e4d50ad02633eebee27ece445197767edeb1ad0a39b61d0c02b934df4e5af03; original global index 4820.
def localCycle00080 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .triangle 4 2, .triangle 13 1, .triangle 34 1, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 3faf5a294abf1d6ea68a70b7e27f989398d4351fb3bde91594e3385b86900657; original global index 4916.
def localCycle00081 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 3 5, .distance 3 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 0, .triangle 31 2, .triangle 33 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 410ef0a6384dcbde6df12dc2f4142b88f1e7fbb87aa14ef803416e703b550f45; original global index 5021.
def localCycle00082 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 18 2, .triangle 23 1, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 42b2a7811317f5e27c4b82537862dd0b2fc4ecc268c45d68eb801f1aab0f5839; original global index 5136.
def localCycle00083 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 44a1edb3b5c340edac922dbf09ed1fcfe4e9100b5fd51fa8a500f95a4d62b674; original global index 5317.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 5 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 17 2, .triangle 3 2, .triangle 14 2, .gapLower 6 2, .triangle 33 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 452a47ad1eaed52a29541673c9edd208a3a137a7ea83002d4d835e7f1df390ac; original global index 5350.
def localCycle00085 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 45e05820658b9e4b160146108c77f43740fb9c567061a0317704fa2ad03c9f5e; original global index 5404.
def localCycle00086 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 5, .distance 3 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 2 2, .triangle 12 0, .triangle 31 2, .triangle 33 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 46c9b5bd77ed4582fb0ab46446e47fc1a04dd308115089a85aff0a7506188606; original global index 5484.
def localCycle00087 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 1]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 1 2, .gapLower 6 4, .triangle 4 1]

-- Original cycle 46c9dda9bf2508eaaf5f3c3a5b2d9a506fc94f0f0a010bdca775d68385ff4b59; original global index 5485.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 4 5, .distance 0 4, .distance 0 6, .distance 4 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 4]
    constant := ![4, -1, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .gapLower 6 2, .triangle 33 0, .gapLower 3 1, .gapLower 4 0]

-- Original cycle 46ec41ee0e17bdc54d47d7ff6ddbebd091ad1e5070505cbeb7990caccad1c198; original global index 5494.
def localCycle00089 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 5, .distance 4 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .gapLower 0 3, .gapLower 5 2, .triangle 31 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 47b5e67dee9ae5e98ecaa5b77696a08294a1874833793b932092b867ef42f776; original global index 5554.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .gapLower 1 4, .gapLower 4 3, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 47c4267d5b65efa2ef233d0cde5596880b7a9272192f924fe5790afc53c077c3; original global index 5559.
def localCycle00091 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 3 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 33 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 486684d1f8ba04e43bb133ce992ae29b9e9645d375a71e2bc68a9419d0411a17; original global index 5604.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 489ed8f7aba1a71c7c2b220c440c023dbf5ca6358b8c637abea7815f0b96dd66; original global index 5627.
def localCycle00093 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 493170a31634eb8320529e5eaa3fdeb516aa97136d17dee5eef8c29e8cc69363; original global index 5667.
def localCycle00094 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 2, .gapLower 5 3, .gapLower 0 2]

-- Original cycle 4932e8deeafa5f83289e2f2032e99e83a44e6edbac33960a2bb137a404a912ac; original global index 5668.
def localCycle00095 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 2, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 4a34a03a82f31ba6a169abb6e01018e0539d5304c2d38c832e03307fde095e48; original global index 5753.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .triangle 32 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 4c5d9bda8194311b19102f2c6fea76f0d18abe360d1a06f488d12e56adb84568; original global index 5929.
def localCycle00097 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 8 2, .gapLower 6 2, .triangle 32 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 4cc0ea30189a0d1f0eb6e065859e8ab6baf08ce4457b7fac82964487e4f955b6; original global index 5959.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .gapLower 6 3, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 4cd93a7f339fe19c9d3e9af19ef0f3d54b4579042de42e6726d59f84a467a590; original global index 5969.
def localCycle00099 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle 4cf5d2c20221a23403ccde60ba7f7e2052ec071ec11aa4207fdae5ccaf7fb082; original global index 5977.
def localCycle00100 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 2, .gapLower 5 3, .gapLower 0 2]

-- Original cycle 4d35c46a8572b0c967cbfc7f3cd0636b8a3aeadc4f0b1bb14b5c7822f04a342f; original global index 5994.
def localCycle00101 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 2, .triangle 23 0, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 2 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 4f49981b09732e9d2cf9cbbdeb216c4f82488d57ffafd43168eac46d44931116; original global index 6161.
def localCycle00102 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 2, .gapUpper 3 5]

-- Original cycle 4f5b875a1284a609c3f4a3b8b555f849c49838b343d3a38cef56adc625199839; original global index 6168.
def localCycle00103 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 0 6, .distance 0 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 2, .gapLower 6 3, .triangle 13 1]

-- Original cycle 4fb6edf5c20d2771e5c0fe364d38c83cce9d0976bdae39be84d58a6110455a75; original global index 6190.
def localCycle00104 : Cycle where
  length := 3
  data := {
    node := ![.theta 5, .distance 5 6, .theta 6, .theta 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 0, .gapLower 6 0, .thetaNext 5]

-- Original cycle 50697ef02e8f4302ce953f5010e57a1ce86a290e49473d0abbf867f56bcd3217; original global index 6241.
def localCycle00105 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 50b75a8c49120bf986191e06fe73a4bc385eee00f483e60988a24232c2ae8a43; original global index 6264.
def localCycle00106 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .gapLower 6 2, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 50c7989feb57d38e0e7b3c4b10365c8b0cb4ba82bea084db94d9890e2acd2fbd; original global index 6273.
def localCycle00107 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 11 1, .triangle 32 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 528d79dc61e7c4f2e19aaf94f539598eb2c0b2bba49cec4ed457d05bfbd60442; original global index 6418.
def localCycle00108 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .gapLower 1 4, .gapLower 4 3, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 52ebc54c601833f25a33d41bc9e27b306047b64c8cd16a5642cc42d94205b098; original global index 6456.
def localCycle00109 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 5453292dd12abbe605d474eb6c4f4f5c019f43edb10aaa4a8ede121114cff807; original global index 6530.
def localCycle00110 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 12 2, .triangle 14 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle 545a67fdc411e7176dec15855b4726cb7b80a55f96a41acc7d094eb4efc745d7; original global index 6536.
def localCycle00111 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .triangle 13 1, .triangle 32 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 54b4775a369b93272d6d66489e222ba8b9496998d3b6d669e6c50fd48c0e440f; original global index 6561.
def localCycle00112 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 4 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 553e34b80fa6cfc0f755944c7d1ed113654d2c963e59c708a8bf67d828f91c3c; original global index 6599.
def localCycle00113 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 13 2, .gapLower 6 2, .gapUpper 4 3]

-- Original cycle 5578aa58b0cdeb516fe6d875703dda955ea12f6b39028a86b1de17f2759718db; original global index 6620.
def localCycle00114 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Original cycle 559b27e78a292acb3e24bcf376400c384e5ed38cf3862b68db73c4b5f5d36103; original global index 6639.
def localCycle00115 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, 0, -2, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .triangle 18 2, .gapLower 6 3, .triangle 13 1, .triangle 2 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 58507811e94e8964f977ccc44ae936fb3f5bace3335b2495dc375ab31bba86ea; original global index 6855.
def localCycle00116 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 6, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .gapLower 6 2, .triangle 4 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 5960e45c05d26e1988b895e10df301e84caa626ca2471627ee84abeb418bc2a6; original global index 6943.
def localCycle00117 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 4 6, .distance 0 6, .distance 0 1]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 1 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 1]

-- Original cycle 5b1e5d2531c49c364c73a17e19c6fa90be98852c66577f13b49d3785abfe0e28; original global index 7091.
def localCycle00118 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 0 3]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 10 2, .triangle 14 0, .gapLower 6 1, .gapUpper 3 3]

-- Original cycle 5b5d573912144228c64a11f7d52fb87c5e92f676a7f6658909416363596d7e45; original global index 7111.
def localCycle00119 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 5 6, .distance 3 6, .distance 3 4]
    constant := ![2, 0, -3, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, true] }
  origin := ![.gapUpper 4 1, .triangle 34 1, .gapLower 6 1, .triangle 32 1]

-- Original cycle 5bf7957264ad171cedd8863f475de1f52adeb2f08371151f623b8a4d5cf0809d; original global index 7155.
def localCycle00120 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 4 6, .distance 1 4]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 23 2, .gapLower 6 3, .gapUpper 4 4]

-- Original cycle 5c151c0308441fcae5aa2d2d40b57a865775fee0d184e7fb04fc312033af75eb; original global index 7168.
def localCycle00121 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 0 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 5c3ecec023570ace9d4fcd7651d844cef3148c3450d8dbe99a0ceda6460f1154; original global index 7182.
def localCycle00122 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 2, .gapLower 6 2, .triangle 14 1]

-- Original cycle 5d5214d548fafedd1cd55ac0947281374bd3fd334a35cb3a24951b3984a4fcef; original global index 7263.
def localCycle00123 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 22 0, .triangle 2 0, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 5d87c147ba38f6325d5292c1b9dbcfa9c956c68197cddaed1f07eb35deae7922; original global index 7279.
def localCycle00124 : Cycle where
  length := 13
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 3 6, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -2, 2, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 11 0, .gapLower 6 0, .gapLower 6 6, .triangle 34 2, .triangle 29 0, .triangle 16 2, .triangle 2 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 5d97c1bccb96074e709bebd6e379e40d230a8a614392eb77d1987b1dab22ea67; original global index 7285.
def localCycle00125 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 17 2, .triangle 3 2, .triangle 14 2, .gapLower 6 2, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5fc645b65ecdabeef5ddd7e8d386fbd2c9d4d77615d8f846960056131fbd44b0; original global index 7463.
def localCycle00126 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -2, 0, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 2, .gapLower 6 3, .triangle 4 2, .triangle 13 1, .gapLower 4 2, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 60aa9c70130aaac5a49022c6fcebad622fbe757dad7a8eaef2cc7e15de9dae71; original global index 7526.
def localCycle00127 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 4 5, .distance 0 4]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 5 2, .gapUpper 4 2]

-- Original cycle 611eda4843648bd6767b7d963b9bc32c11a286c501a05bac3184af759851a494; original global index 7576.
def localCycle00128 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 4 6, .distance 3 6, .theta 6]
    constant := ![3, -2, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 18 2, .triangle 23 1, .triangle 32 2, .gapLower 6 0]

-- Original cycle 63357cec14119450d7077ee6faad9391b8f2d026e6feb1ee04d1830c0419f3c1; original global index 7740.
def localCycle00129 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .triangle 11 1, .gapLower 6 0]

-- Original cycle 636eb782be913424bca10fc02510cf806e967007fd74d194b83a2fec4f5831d7; original global index 7759.
def localCycle00130 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle 641c8588f6b5acfbd6de5e35f6a61599d93d1454611a9e3a2cb66e8a42710ff2; original global index 7799.
def localCycle00131 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 642d7f295bd9cb658e61728d7116cd6c380c00abaf4611d61e59f7ca52527595; original global index 7805.
def localCycle00132 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 14 2, .gapLower 6 2, .triangle 32 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 648cfe6ded0d6e62f135752e42a443b7e81f256ed4e4ef1a333dd1b2f12c3526; original global index 7835.
def localCycle00133 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 2, .triangle 18 2, .gapLower 6 3, .triangle 13 1, .triangle 32 2, .gapLower 6 0]

-- Original cycle 648f44ac76c1aed44baa4b3f740d2a0206bb7aa2bbbad32fdcbcee05e1b1b957; original global index 7837.
def localCycle00134 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 4 6, .distance 3 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 2 2, .triangle 12 0, .triangle 34 2, .gapLower 6 2, .triangle 33 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 663e7cf6267b8521b615dd2cac8220c7a33a548420921442808a97a3b79896ee; original global index 7953.
def localCycle00135 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -3, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 6 2, .triangle 13 1, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 66583a8cdfc6ccc3e687054b706e58c3c2e190564d4d70c4e09d2569a99bcdc1; original global index 7958.
def localCycle00136 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 3 5, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 18 2, .gapLower 6 3, .triangle 14 1, .triangle 33 0, .gapLower 5 0]

-- Original cycle 66b60b1820266d6a67d2cb762d086539a625f21846d5f247f46fd6aa192840c7; original global index 7984.
def localCycle00137 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 13 2, .gapLower 6 2, .gapUpper 4 3]

-- Original cycle 681916876fe9ef51a8825e211085831cd676a1bd2b5b3a3b0cc1dab5d46965d9; original global index 8090.
def localCycle00138 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 6 2, .triangle 13 1, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 685c208d9112b2bf4a1123720f9c0ce11be6b0cf1c8715207a929d3f40d4f3cf; original global index 8116.
def localCycle00139 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -2, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .gapLower 6 3, .triangle 13 1, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 6887827c9e8cefa768f2e28479769f2d0c980c19b84d4b3f624219f5d05ba5ba; original global index 8130.
def localCycle00140 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 3 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 0, .triangle 34 2, .gapLower 6 3, .triangle 11 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 68b6a6785817e81733c04587873e0b160ec91d7176961d2f1c0e5f88de4d15b8; original global index 8145.
def localCycle00141 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .gapLower 6 3, .triangle 11 1, .triangle 32 1, .corridorLower 3 4]

-- Original cycle 69ad4ad7dc91d362d42024a4796ef201f971ccd5dd4112396f8d386526b6cc91; original global index 8226.
def localCycle00142 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 2 0, .triangle 4 0, .triangle 23 1, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 6a81de1399bfa92936d7d68945d28d8d57f913f59b5216a34d3766d2453594f6; original global index 8293.
def localCycle00143 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 4 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 6ae35bf61937f3820e853939c70e45b5d36aada334acf036b04d4b47561e8e3e; original global index 8322.
def localCycle00144 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -2, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .gapLower 6 3, .triangle 14 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle 6c49ccd2ce0627d7b089d78457e2a3f2939b1705c852b93dc27e7b75e3e98df1; original global index 8436.
def localCycle00145 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 5, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .gapLower 0 3, .triangle 7 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 6cac7d9c543b0ad11d1cc2937a70691e1ed3fd9028871353e617b86b38534512; original global index 8455.
def localCycle00146 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .triangle 13 1, .triangle 32 2, .gapLower 6 0]

-- Original cycle 6cba4fabad2ebf2a8585a0e06ef309d44a1dd54be07ea2d17d7aa4b27dd41ddd; original global index 8460.
def localCycle00147 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 5 6, .distance 0 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 0, .gapLower 6 2, .gapLower 6 1, .corridorLower 3 6]

-- Original cycle 6cbf357ee46a2669ca077b4d54409d62e0f88af39603cdfebdbf459fd1813c8c; original global index 8463.
def localCycle00148 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 13 1, .triangle 32 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 6eb4f1541efe3c2d3cbe84c7363eab5ab7893efcc1b782c618e3101fcdabc81a; original global index 8589.
def localCycle00149 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -3, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 6 3, .triangle 14 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle 7114ee54f694569688c7c7179f6faec16758996692259c2baf0a345bf9634c83; original global index 8773.
def localCycle00150 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 5, .triangle 4 2, .triangle 11 1, .triangle 32 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 71340337b4e1b34780682788b6a78aa9e3e8e543561137a53c8c8d600b6fbfc8; original global index 8780.
def localCycle00151 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 13 1, .triangle 32 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 71e9b9ac17597394b5542f037af1db1e40b63f7ef6c57f91e3412b54f116cead; original global index 8829.
def localCycle00152 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 2, .triangle 2 0, .triangle 4 0, .triangle 23 1, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 72d3d35a5f3870b301d40f591dabc89485f2b66e11b967c2cc4e14771e150704; original global index 8896.
def localCycle00153 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 4 5, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![4, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 28 0, .triangle 29 2, .gapLower 6 5, .triangle 4 2, .triangle 11 1, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 73f3314f4e3bc7b3a2fc330678151e604a6bccac0d804a996ceb7b92b054f581; original global index 8993.
def localCycle00154 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 17 2, .triangle 24 0, .gapLower 6 2, .triangle 11 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 74050b710f8db71d9a869abe32ca96a794d6c1ad037e562f21f1a67774e2533a; original global index 9001.
def localCycle00155 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 7408dad13d7ebff7119c8bad89859cb49ca0e8adbd125c674f166658f2872dfe; original global index 9003.
def localCycle00156 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 13 2, .gapLower 6 3, .gapUpper 4 2]

-- Original cycle 76f53c50a8ee2d86a45cc883ae82bbd85d907fb26a8eb9648d7851c513300d55; original global index 9207.
def localCycle00157 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 6, .distance 4 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle 7808c8dd1d18619e9a89b467f63505d896dabfd898ee036574fda80d4023688a; original global index 9280.
def localCycle00158 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 789ba225e02d1e878bd86f3c7868f8929b59a05c163c5f758c6c9f7f1b76abfb; original global index 9329.
def localCycle00159 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 29 0, .triangle 16 2, .triangle 2 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 7950caec5b5935d68587051848aff82f359cb4dd94edfd535af42856de15fbb6; original global index 9386.
def localCycle00160 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .triangle 32 2, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 7a32b6654f23f53e436d719b8664e651dad388cf5ed88dbc4e52d663e9320f03; original global index 9450.
def localCycle00161 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 7a4041cb9391b44f7ec0e7ea7fcb60a0e0a5edb204d07415791864bc0a32b568; original global index 9456.
def localCycle00162 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 0 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .triangle 3 2, .triangle 10 1, .triangle 31 1, .corridorLower 3 4]

-- Original cycle 7a6ce8a4022ae2c3abab18d33a27917855c50c69b6e98452254585199f5dfbb0; original global index 9473.
def localCycle00163 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 4 5, .distance 3 5, .distance 0 3]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 0 4, .triangle 12 0, .triangle 31 2, .gapUpper 3 2]

-- Original cycle 7aabb5bf469a40bd16e20bc36e70505178626796a27df0336b1a31e53262a7ee; original global index 9495.
def localCycle00164 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 7ae3e4df0201026f0e988bea12823c1e6e0b99cbed8ba373ef677aa8146f1818; original global index 9513.
def localCycle00165 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 2, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 7b7faf316ac15257e0bc1520a192b509eb09e463307e743db4003400c6901d4f; original global index 9557.
def localCycle00166 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 7c186063f85462d5deb61cba8916481c080c299c71329986205d3afb1fe4760d; original global index 9601.
def localCycle00167 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 2 0, .triangle 0 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 7c20fb731ed2fcc283c4c0b9a70a79048f8b89339e0c31d8dc242569223dfba6; original global index 9604.
def localCycle00168 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 2 0, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 7cc5b77f7a37f9df1e0c248c48adda039326a8fc96cd6876375bd33cd98fb286; original global index 9665.
def localCycle00169 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 7d660e3513dd679dd9470e19a34a3327481d3242f9de8d71f3422bb32d5b5ada; original global index 9720.
def localCycle00170 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 0 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 24 1, .triangle 14 2, .triangle 11 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 7f630c78fde5d47e6dee48cf671327f564470af18baf68a73e09fab6cc0e2fd6; original global index 9879.
def localCycle00171 : Cycle where
  length := 4
  data := {
    node := ![.theta 3, .distance 3 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 0, .gapLower 6 2, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 8357c0d652ca57c2105b99acb1a4bec43806a14a506cb2322b9b6c685f8469ed; original global index 10185.
def localCycle00172 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .triangle 14 1, .triangle 33 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 8394d4c32b2d570f0df61e9c22238270e939f9384eb05d680e571e0d0eae2f72; original global index 10214.
def localCycle00173 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 2, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 8503de010a0f0af5c05494b134378924e0653d8fb5c297bc2669379b669b8bb3; original global index 10324.
def localCycle00174 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 9 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 87272f2c20d69bb5c0d27cd4b56059147b1dc47db9257a7bc7a3d66c504a5fb9; original global index 10486.
def localCycle00175 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![4, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 11 1, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 87fc3ccc56a61fba9812689a1e1dcc338701a664bc14463fabb34bbd816ff55b; original global index 10541.
def localCycle00176 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 5, .distance 3 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 2 2, .triangle 12 0, .triangle 31 2, .triangle 33 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 882aa5cb672694d2ca75360c8080ebfa3b1f164894b6db0035d21859f4f7749f; original global index 10556.
def localCycle00177 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 3 6, .distance 0 3]
    constant := ![0, 0, -1, 0, -2, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true] }
  origin := ![.triangle 10 2, .triangle 12 1, .triangle 13 0, .triangle 34 1, .gapLower 6 1, .gapUpper 3 3]

-- Original cycle 88d241b7cb5781f1d272dac5d888dd824bd672274db34dcba4d737e66b4126b7; original global index 10599.
def localCycle00178 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 0, .triangle 16 2, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 88d89ebc65b4c17fc37e5c5061d11d83e2643063c20dbb4d2efd4e83c05acc1d; original global index 10601.
def localCycle00179 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 18 2, .triangle 24 1, .triangle 3 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 8961e3482401802607b4e2eaeb06c76d8ff56260ad9b7b781c093f2594472421; original global index 10629.
def localCycle00180 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 897dba1c5c5f47f91331b03721dac88a8e1f3fde40c391d639a01b6fdd1002d5; original global index 10645.
def localCycle00181 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .gapLower 6 3, .triangle 13 0, .triangle 2 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 8aaaa1b3cefe4542b80627ea01765ce28909b73b24785ced95bec18fdb06a4a8; original global index 10743.
def localCycle00182 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle 8cb8a0b81a1fd90dd7e7c7f427f385ab64c926aaddb27a011b437cb5e23f3bf8; original global index 10883.
def localCycle00183 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 0, .distance 0 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 0, .gapLower 0 6, .gapLower 0 5, .triangle 9 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 8cce266dbd56400ef0c08995ccdbcefe18d565952099f92a8ffe3becc4d94c28; original global index 10889.
def localCycle00184 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 8 2, .triangle 11 1, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 8d597f1516255a68be28bce761e8a2cb776026b74df147b7c8f5b88753bfb42a; original global index 10929.
def localCycle00185 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 3 5, .distance 5 6, .theta 6, .theta 5, .distance 4 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, 0, 3, 0, 0, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 10 0, .triangle 33 0, .gapLower 6 0, .thetaNext 5, .corridorUpper 4 5, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 4 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 8e4d4d3e16965f677d40815c6921a494ca04d0886c0e62d1d27d03fa0386a57a; original global index 11017.
def localCycle00186 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -3, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 24 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle 9037d595ef22e55432ec10e8e2a360bc3e79944819e1cf2ac671011a680df834; original global index 11165.
def localCycle00187 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2]
    constant := ![2, -3, 0, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .triangle 4 2, .triangle 8 1]

-- Original cycle 9052c16db71e3ac8dec906e891af65dcfc37ac2873b2d5f9f6ef87d1c74f2e83; original global index 11173.
def localCycle00188 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .triangle 13 1, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle 90ff26b94b9aec5b5aef848065f40bff30b3f5ce8a7060cc59129bba67c4e06c; original global index 11228.
def localCycle00189 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 0, .triangle 3 0, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 913e62bdd8aaef9146708d2196c373ed34329db59b3ce572e4eb3d8f31620154; original global index 11251.
def localCycle00190 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 1 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 18 2, .triangle 24 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 9142c77703d4ea58b8e823cb29d03aa0ce8798f80c803d2ff87ea8bf548e1727; original global index 11252.
def localCycle00191 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 1, .corridorLower 3 6, .thetaLower 3]

-- Original cycle 93276a2c619d086085daa149fdfa90c376b5c1bea3b043244741e3c4e9b3cb4f; original global index 11408.
def localCycle00192 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 2, .gapLower 6 3, .triangle 4 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 93c35ead1091d99a3c32117817830418d4c06047b76f1b60914c762a32ec5c14; original global index 11465.
def localCycle00193 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![-2, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapUpper 2 2, .gapLower 5 4, .gapLower 5 3, .gapLower 0 2]

-- Original cycle 9407f18a27cde3520b1553ac5e5b470595dcbfc8e6b3a67fdb04d16a382f9694; original global index 11482.
def localCycle00194 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .triangle 14 1, .triangle 33 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 9440d9d877fb69d177e6cdbd58bb658dc9b3325e4dc8c255376325bfccc9bfe6; original global index 11502.
def localCycle00195 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .gapLower 6 3, .triangle 13 1, .triangle 32 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 94d2c435955dd6c4bbd8e8c6a69412231e6fa74f536bbb44efd8a028a24a95a5; original global index 11552.
def localCycle00196 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 6, .distance 3 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 23 0, .gapLower 6 2, .triangle 11 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 9660b388c2cfe10dee3ae58fe58f917f64d5c1465b915a52072aacb73822c329; original global index 11691.
def localCycle00197 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 4 6, .distance 0 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 6 3, .gapLower 6 2, .triangle 11 1, .triangle 32 1, .corridorLower 3 4]

-- Original cycle 985db4502f71bc12fe95af01895334c6d27c703f129f94295a30f58e4a1e8c73; original global index 11832.
def localCycle00198 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 986bbb60263426d749adeebd0300d2e866bd84a74558074aea5d006d9699ead6; original global index 11837.
def localCycle00199 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 2 2, .triangle 12 2, .triangle 14 2, .gapLower 6 3, .triangle 32 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 9932f0976bea4854aca4883ee8ef4c7a26df5c74b0d712afef13adc53c59a593; original global index 11897.
def localCycle00200 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 0 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 24 1, .gapLower 6 2, .triangle 11 1, .triangle 32 1, .corridorLower 3 4]

-- Original cycle 9994ff1edc4a2cf94470d94b5ee838cf33e40707b9120a78a92a394fb7698f15; original global index 11924.
def localCycle00201 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![0, -2, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true] }
  origin := ![.triangle 13 2, .gapLower 6 3, .triangle 34 1, .gapUpper 5 2, .triangle 12 1]

-- Original cycle 9a273e402fe3820342838593720e39b3b771246fb0ead88c519c9bd7e10d8a15; original global index 11972.
def localCycle00202 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Original cycle 9b7320a177d5a62ccbcef966647f73a939ab49912a9384ca5be5fefa181d08e9; original global index 12092.
def localCycle00203 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -3, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .triangle 14 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle 9d04ad2b37561ca294af4fc302dbdc77465d915d7f46306d5f277d113e0a56d0; original global index 12213.
def localCycle00204 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 2 6, .distance 2 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 5, .gapLower 6 4, .triangle 29 1]

-- Original cycle 9da6dfec8384cfc8069b1b10bf7a55a3abb8b8fa8fe352a6c59e2f4bba1a1427; original global index 12263.
def localCycle00205 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 3 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 8 2, .triangle 11 1, .gapLower 6 0]

-- Original cycle 9e1ea080391236e1405dbb8502c75a7f26721f5f616fb4d586b20ddfe6399af1; original global index 12307.
def localCycle00206 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 0 3]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 9 2, .triangle 13 0, .gapLower 6 1, .gapUpper 3 3]

-- Original cycle 9e74d58ab2d95ff960873882eb99269de5d23f4b213411545d217ca8121b5386; original global index 12341.
def localCycle00207 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 0 1]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 0 1, .gapUpper 2 2, .gapLower 5 4, .triangle 3 0]

-- Original cycle a19c3c98fa9c441cf75fd99db347e1cfe391bdae05f0d7cc8d0900db2ef83f43; original global index 12566.
def localCycle00208 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 2, .triangle 22 0, .triangle 12 0, .triangle 2 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle a1abdccdbcaca3a2a18ceb8aeb6d286eb4993e8dfa25cb07b7c61c457ea3038d; original global index 12578.
def localCycle00209 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -2, -2, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .gapLower 6 3, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle a28349603f73175f634033808162d603900d26085574469db540bfbf1ce57eaa; original global index 12642.
def localCycle00210 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 6 2, .triangle 13 1, .gapLower 4 2, .triangle 31 0, .corridorLower 3 4]

-- Original cycle a3a240c4f88efcc08605f2dac17bc8b45bce44b83e92b7ed1881002c41149db5; original global index 12719.
def localCycle00211 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 0 6, .distance 5 6, .distance 3 6, .distance 0 3]
    constant := ![0, 0, -2, -2, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.triangle 10 2, .triangle 14 2, .gapLower 6 2, .gapLower 6 1, .gapUpper 3 3]

-- Original cycle a63c2b2e25adfedb49d55afe2f230f1db545ff79913bd16199c39d1795c845c0; original global index 12914.
def localCycle00212 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 2, .triangle 2 0, .triangle 4 0, .triangle 21 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle a663e52312a32be128a0e1a4fde29cc4dc4769ad7f1634977b2ec6625b533c48; original global index 12928.
def localCycle00213 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 1 6, .distance 4 6, .distance 0 6, .distance 0 2]
    constant := ![2, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .triangle 23 1, .gapLower 6 3, .triangle 8 1]

-- Original cycle a6e5e510de0cdce006830e496dcbb5e61ddc8d2c389ed897971c118930d2bd81; original global index 12964.
def localCycle00214 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Original cycle a737e549ed09a86c21ab0c21b1bee71b84039e2d752eae63edbb4a127d0b4580; original global index 13000.
def localCycle00215 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -3, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .triangle 4 2, .triangle 13 1, .triangle 32 0, .corridorLower 3 4]

-- Original cycle a74e3eeff7e3f30acd6121d9e3dd35ce6279739ad0d40c79ccda1685c2ffa489; original global index 13012.
def localCycle00216 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 2, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle a788dd2f86de12b45ad28537ab200f593b037955532650e7814bcfc0df498d44; original global index 13034.
def localCycle00217 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 24 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle a91f9caee774edf7d1941dc8795be5b01f46f354e218768bc1c57c720ccd1a30; original global index 13167.
def localCycle00218 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Original cycle a95c4e2c694e5bc912d8f45b13291455dd93280bf7b103aab83f3b49ba6322b9; original global index 13187.
def localCycle00219 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 23 0, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle aa594535690479e26f43bc407058c559ba2dbc69eec8c29abaeae8e4560ccf3b; original global index 13266.
def localCycle00220 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 3 6, .distance 5 6, .distance 3 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 33 2, .gapLower 6 1, .gapUpper 5 1]

-- Original cycle ab336e54cafc0b2505adb34c5b0037ec34b8479e2155f25d8471c9409ac90272; original global index 13337.
def localCycle00221 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 5 6, .distance 0 6, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 0, .gapLower 6 2, .triangle 4 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle ab3582250043336750c327a125b744806d6abeb0585f7025960b8fdd2ef21b44; original global index 13338.
def localCycle00222 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle ae4954375904c97886acd239713461b90c01da6dc88a6b182a2d1dd3ca904689; original global index 13601.
def localCycle00223 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 18 2, .gapLower 6 4, .triangle 13 1, .triangle 32 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle b0e8030c42a7d099e2134bfd2ebd8e181e1e0787be83667ea43205f9c83dc297; original global index 13812.
def localCycle00224 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .theta 6]
    constant := ![3, 0, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 29 2, .triangle 18 2, .triangle 4 2, .gapLower 6 1, .gapLower 6 0]

-- Original cycle b10dc9ea4a279dea1b666d80c9f3e94a02f642a4079cda8a84f12f800c4e37b0; original global index 13822.
def localCycle00225 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -2, -2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle b1363f1045d65657309054786e4ac90f129f90b566cb1bfd147285213650f37f; original global index 13840.
def localCycle00226 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 5, .triangle 4 2, .triangle 13 1, .gapLower 6 2, .triangle 33 1, .corridorLower 5 6]

-- Original cycle b286860016e0718714e096f74fd50ca9ea02abebec8803990de2d2193d80fdf7; original global index 13953.
def localCycle00227 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 5, .distance 3 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 2 2, .triangle 12 0, .triangle 31 2, .triangle 33 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle b2c29ac8fb721bbce2cde5285bc241703b7d8cf058385e341963f4477c8fb921; original global index 13973.
def localCycle00228 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle b2fae72b9fd74e3362b9044da026fc41dae5b9d14613367029c7acdbd6f45009; original global index 13988.
def localCycle00229 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -2, -2, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 2, .gapLower 6 3, .gapLower 6 2, .triangle 13 1, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle b32b03d09095687ab482069cb332146b8f67c22aa8d3fdeaabf908572a16ad11; original global index 14001.
def localCycle00230 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle b46fb9e6edc21c8002c8369c356c000e1be92c9dc01a4ef23645ab97aa0e44fa; original global index 14096.
def localCycle00231 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .gapLower 6 4, .triangle 8 1]

-- Original cycle b56400a7bf2c444a288df5080daab3f3fecdcac73937682620c4b704c0b310b8; original global index 14169.
def localCycle00232 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 2 2, .triangle 12 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle b59d5b72c42f77129a9912e2b845457e2cc92b41421b2d38ed508691c2b87779; original global index 14189.
def localCycle00233 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 8 2, .triangle 11 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle b5af853eb828b611955d6ff190f85f2feba0225b931a1512ebee7aa624bb4da8; original global index 14197.
def localCycle00234 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 22 0, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle b6a561dd6c5c2cd289aa6033e0d5193c6c8670cf4fa95f79f17f09041f74fe80; original global index 14275.
def localCycle00235 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 18 2, .gapLower 6 3, .corridorLower 5 6]

-- Original cycle b7a036bb63029f998d43068f7645f3a22ecdc95497822dfe22f87b43794748bb; original global index 14327.
def localCycle00236 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 13 1, .gapLower 6 2, .triangle 33 1, .corridorLower 5 6]

-- Original cycle b867e4d5f2a4af4b5b377a548e40beae545bf5f18c7775ad1c5f29b69b7338a3; original global index 14390.
def localCycle00237 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 3 6, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -3, 3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 11 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle b8c956136791fc950d6a53287da875fdd6a7e7bff8a45f6ed87c43887685bdd6; original global index 14421.
def localCycle00238 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle b931a68369f4809f725dd0252a30ae3fd8dd0faa2f6ba173ccf75eb8eeb1bebf; original global index 14451.
def localCycle00239 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 1 6, .distance 5 6, .distance 3 5, .theta 5]
    constant := ![3, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 24 1, .triangle 33 0, .gapLower 5 0]

-- Original cycle b95ecb5e3d9f7c923e8f0a988d664dacfc79fdc5e110f0e54252acd2c03bce79; original global index 14464.
def localCycle00240 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 2 6, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 30 1]

-- Original cycle baa403489bede10938127b4c9ddf4d55c23e963092ff35edb6ce6dc88d878292; original global index 14577.
def localCycle00241 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -2, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 6 3, .gapLower 6 2, .triangle 32 0, .corridorLower 3 4]

-- Original cycle bad6d792bbfd431ba1071e8a76dac2cf34565f8b164aac358f55b4179bdfbe84; original global index 14594.
def localCycle00242 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 2 4]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 2 3, .gapUpper 5 5, .gapLower 6 5, .triangle 29 0]

-- Original cycle bae5a2aacca9e45087dce3148a62c2a0f480c9ea74ea4df820bee180db0e22d9; original global index 14596.
def localCycle00243 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Original cycle bcb3f80ec314578398313c6145c0dfa675d6c33b72f422414e088913eb8eef86; original global index 14718.
def localCycle00244 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 3 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 0, .triangle 34 2, .gapLower 6 3, .triangle 11 1, .triangle 33 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle bcf677990e15cec764b9bc98b6e80c5aafb60c05d90294fac13b0f8d53f35cda; original global index 14743.
def localCycle00245 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 4 6, .distance 1 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 23 2, .gapLower 6 3, .gapUpper 4 4]

-- Original cycle bde679e56ac556581dbb5217e1b8d50120241d845873849d8a373c32ebf6e80f; original global index 14811.
def localCycle00246 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 0 1]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 0 1, .gapUpper 2 2, .gapLower 5 4, .triangle 3 0]

-- Original cycle be0b7f0e012461fef9ac18a287340fd565d1cef99f315b52ded441edd61004d4; original global index 14819.
def localCycle00247 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 1, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 29 0, .triangle 16 2, .triangle 2 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle befc1b1bd7fb4ea4fb2bcb0eb6db774a6c6b8daebddbeea5e5279b7bb5282ebf; original global index 14900.
def localCycle00248 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![4, 0, 0, 0, -3, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 9 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle bfeef606de6d26a36c32b2f043e3543af627bacbba9dcc0eab515f79c470597e; original global index 14977.
def localCycle00249 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 2 2, .triangle 12 0, .triangle 34 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle c03102d0536b4a55dfb786f0f0f4515909c0b6f2909f08ac93096868c28c69a0; original global index 15003.
def localCycle00250 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 3 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle c083025ed38206a62fff47baafc3aeb33a45c8aadb1a5ed93e16c35f353a5b09; original global index 15030.
def localCycle00251 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .gapLower 1 4, .triangle 22 0, .triangle 12 0, .triangle 9 1, .corridorLower 3 4]

-- Original cycle c0f0fae824e602530aa79a0adebc96d0c4e9eef39eb9b26cf17d2a4f0f23c21f; original global index 15065.
def localCycle00252 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, 0, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .triangle 18 2, .triangle 4 2, .gapLower 6 3, .triangle 32 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle c1227d45053825f028f387d7266f0e183252ecee36d1f7d69e02e8df7b15d612; original global index 15075.
def localCycle00253 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 5 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 17 2, .triangle 3 2, .triangle 14 0, .triangle 33 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle c157ddbd40c1ae1046e9b69805baa8db64c8a7fd46a687f104ce5175591211c1; original global index 15096.
def localCycle00254 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle c2606bebbe346d46f66360e3c9ee272594c3094d1bc8485a7aa0041cffa84159; original global index 15175.
def localCycle00255 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 3, .gapUpper 5 3]

-- Original cycle c3d2b98675ddf2e8610d3e117f236f7ea0dff29869ef922e76778026b69e65ba; original global index 15277.
def localCycle00256 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 4 6, .distance 5 6, .distance 3 5, .theta 5]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 2, .triangle 2 0, .triangle 4 0, .triangle 23 1, .triangle 34 1, .triangle 33 0, .gapLower 5 0]

-- Original cycle c47e37abe7d38e2bfe150585ddcf81620debf02fa6e0367fa3652bc4ba1ff861; original global index 15321.
def localCycle00257 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 5, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 2 2, .triangle 12 0, .triangle 31 2, .triangle 33 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle c4b7804d9aa27073a511d1821d08c764a9e8b26475076bb59a7adf15b49f391a; original global index 15342.
def localCycle00258 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 0, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle c60eeeaebe9c349394362ed1954b6e7d9c046c879e16b0e698d1996f586d9ef7; original global index 15446.
def localCycle00259 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, 0, 0, -3, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 2, .triangle 4 2, .gapLower 6 3, .triangle 32 0, .corridorLower 3 4]

-- Original cycle c6496805ebf8de892960b21ff38ec9d1de6c1e7c56a30a5904896ec449d9cb2c; original global index 15465.
def localCycle00260 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 4 6, .distance 3 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 2, .triangle 18 2, .gapLower 6 3, .triangle 32 2, .gapLower 6 0]

-- Original cycle c67f1bdc3ceff8e2379a52d5177dc333838bd5e625cf084875c3f4814dfe6bcc; original global index 15482.
def localCycle00261 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 28 0, .triangle 29 2, .gapLower 6 5, .triangle 4 2, .triangle 11 1, .triangle 32 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle c7ba3c0ae1b30fece3c0655d51ffed609601ff691277180f18221b10084e93ad; original global index 15592.
def localCycle00262 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 4 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c8943c10308135bab1f323d70235f18a6ef9cc32f09ef80436dcd81d117a369f; original global index 15666.
def localCycle00263 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 1 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .triangle 23 1, .triangle 32 0, .corridorLower 3 4]

-- Original cycle c92a6bd5fb3cdc8aa8269ca0e8d1dac09b8101561021037b04db808d32b8eb8c; original global index 15721.
def localCycle00264 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 2, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle c965e99ea79d58053244c5abcc0db1ecea1780c2e89350a31cb44a66e54c531f; original global index 15743.
def localCycle00265 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 6, .distance 3 6, .distance 0 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 11 2, .gapLower 6 1, .gapUpper 3 3]

-- Original cycle ca371b9f331e6b39cd5de7c61d883b6c1dee639e9a9916a6d0a89f30f9d85944; original global index 15803.
def localCycle00266 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 5, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .gapLower 0 3, .gapLower 0 2, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle cd72a721fc71abe1cfdcadebbf882688a515fb5940449c5266e088fba8b89a67; original global index 16059.
def localCycle00267 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 3, .triangle 32 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle cdda5278bb7966d006cf11504e33d66eced294edf4b4b6e5c9fceb2e8dcc1cce; original global index 16076.
def localCycle00268 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 2 2, .triangle 12 0, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle d01a5a3f62c9072110c37a1bc21d743522da9ec575456efab61a10e8ec4593b2; original global index 16243.
def localCycle00269 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 28 0, .triangle 29 2, .gapLower 6 5, .triangle 4 2, .triangle 13 1, .triangle 32 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle d16c4fcca33722c65bb15b5b3040aac640bfda50bf5583767eef671ea1527796; original global index 16349.
def localCycle00270 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 3 5, .distance 3 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 0, .triangle 31 2, .triangle 33 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d1ab4f69bc0b254c8a668bf3be34f6d7c50ebe495f7702975550fe2f934532b1; original global index 16365.
def localCycle00271 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -2, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 18 2, .gapLower 6 3, .triangle 13 1, .triangle 32 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle d2aadbf22e35595e6b53db52cc207b66e12f211171e0157d1826758a7b6cd80d; original global index 16440.
def localCycle00272 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 1 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -2, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .gapLower 6 3, .triangle 32 0, .corridorLower 3 4]

-- Original cycle d57065b0fe1bf4709376d98b94aa75aa59dd277b836da86ee03deffcfe804ff2; original global index 16663.
def localCycle00273 : Cycle where
  length := 4
  data := {
    node := ![.theta 3, .distance 3 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 0, .gapLower 6 2, .corridorLower 4 6, .thetaNext 3]

-- Original cycle d59e3b7a9c83532d4b98bc9c1ac58124d48c802072f6d009918271363ed9e448; original global index 16674.
def localCycle00274 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 13 1, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle d66f6a773f0d8a48747a2b932eb754dc1efa20caf212ea10e8a04a9f94fad98a; original global index 16740.
def localCycle00275 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Original cycle d8211993e9276e4d4865f6862e16e775dcdfd1dd249c5c6c1e98e581e5e69bc2; original global index 16871.
def localCycle00276 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 8 2, .triangle 14 1, .triangle 33 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle d89531f91da5ca5fb5fae1ce3ac232d45262e02f04b658b604da183f65ee247b; original global index 16903.
def localCycle00277 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .gapLower 1 4, .triangle 22 0, .triangle 12 0, .triangle 9 1, .corridorLower 3 4]

-- Original cycle d92c6c594e1e4558077cf5080121cdc7649bef6f14cc3bf93ffee513eda35842; original global index 16968.
def localCycle00278 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 18 2, .gapLower 6 3, .triangle 11 1, .triangle 33 1, .corridorLower 5 6]

-- Original cycle dad4923fce9a7f60b4b0cb1245beb62549843757b329c29e9775b618e9a38ef7; original global index 17101.
def localCycle00279 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle db302b0c15e624ccba9aae9441f94509cedee36eb2c87b8dfc246bba7a302fec; original global index 17131.
def localCycle00280 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 4 5, .distance 4 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 9 2, .triangle 12 0, .triangle 34 2, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle dbf9ad2cbe420dfaaaadcf44af9f9d379f542af4d9d1ffe32b223d663a807c24; original global index 17195.
def localCycle00281 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 3 4]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 4 1, .gapLower 6 2, .triangle 33 0, .gapLower 3 1]

-- Original cycle dc3428e1c082e2bc8cc24558dcda89193646540556610b1dbd886063e6204516; original global index 17208.
def localCycle00282 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 0 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 13 2, .gapLower 6 2, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle dd6d94d54c1f1fc4558cdcf564f29f91f6d9525e48a190cb096bf4dba3a617be; original global index 17310.
def localCycle00283 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 3 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle dda8cb2779207daad6f10cbedd5e60af189f6b92b33124e02c524d7426b4a469; original global index 17327.
def localCycle00284 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .triangle 11 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle ddd2b19788381b1e37a0ce41115f63503e22085a6e1c63488eb002235dbce064; original global index 17341.
def localCycle00285 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 2, .triangle 33 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle e0ed19594d9baf214cb8cbe1fd92c69bad59ebb7b19bfc8e0099ab94b9f0a232; original global index 17588.
def localCycle00286 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -3, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 2, .gapLower 6 3, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle e1079793812d0efb73d50e8c6a7c65cee76f2ae7f4b3dd7f021a394cceff2c71; original global index 17593.
def localCycle00287 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 0 3]
    constant := ![0, -1, -3, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 9 2, .triangle 13 0, .gapLower 6 1, .gapUpper 3 3]

-- Original cycle e1c5b5c1061789d1be02da4c4ebc2908e01c4e219c9a595db9058ec1f0e2d598; original global index 17654.
def localCycle00288 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 3 5, .distance 5 6, .theta 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 10 0, .triangle 33 0, .gapLower 6 0, .gapLower 6 6, .triangle 23 0, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle e1e2ab9d2433997e99582b1f0a6ca4f53d5825b1803e3b3c964ae4be8f5cb943; original global index 17664.
def localCycle00289 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .gapLower 6 4, .triangle 23 1, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle e3e77e085975aeb4c34f82893c9d1d71a77a22cf0e79f81e44c1a3163b6b6d4d; original global index 17830.
def localCycle00290 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 3 4]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 4 1, .gapLower 6 2, .triangle 33 0, .gapLower 3 1]

-- Original cycle e4954ecd4518a62efe80e466c000638a7c6abe02e7877fdafc7c83f8609c635e; original global index 17868.
def localCycle00291 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![2, -2, -2, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true] }
  origin := ![.gapUpper 3 0, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle e49883e3190c2c9b4621bf6bcd2d0e017f68c1cedd00406b670065d2cafc9166; original global index 17872.
def localCycle00292 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 9 2, .gapLower 0 3, .gapLower 5 2, .triangle 31 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle e4abdb849f505db8f5276ffa53afa325c49006eac7c8950e08ed53c52eaa4f6c; original global index 17877.
def localCycle00293 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 3 6, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 1, .gapLower 6 1, .triangle 33 1]

-- Original cycle e55820277ab0aa33c3ce25a27d10573e221fe1227ccdc7b733f78c2a3fb06260; original global index 17931.
def localCycle00294 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 6, .distance 3 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 2 2, .triangle 13 0, .triangle 32 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle e5984f832a3d75469bb8f5c99ca8883c1c693fb4c65a3ba28df9c4190bbc4a24; original global index 17961.
def localCycle00295 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .triangle 32 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle e72cbada856f3fdbc7d93d16061d16bdf38a41bd89756a2b798e6ea9b534db77; original global index 18081.
def localCycle00296 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Original cycle e885136a496788c1c4f4d6c3ac156d041fec0f449421c0f00cd26847fcf4755a; original global index 18174.
def localCycle00297 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 4 6, .distance 0 4, .distance 0 1]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 1 2, .gapLower 6 4, .triangle 13 0, .triangle 2 1]

-- Original cycle ecf6ddb9936bc7d7d7078b04e87c6983a221aeb60d667fc9ea9b1a472a8c22e9; original global index 18497.
def localCycle00298 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 14 2, .gapLower 6 2, .gapUpper 5 2]

-- Original cycle ef2dda0a6005a0f95228a6b91ef52d1aadbcb69e381a77ae47b358720c5f0fc9; original global index 18662.
def localCycle00299 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .theta 5]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .gapLower 5 0]

-- Original cycle ef6a8dcc8e97edb36e6fd545fbc59a2fa590874fc4eefd3b340c1823846ecd18; original global index 18681.
def localCycle00300 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![-1, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.triangle 13 0, .gapLower 6 2, .gapUpper 5 2, .triangle 12 1]

-- Original cycle efcad9d7e246b0bab88e4537b7013caf1943d3e06c3006eee2ae08b3854e6c60; original global index 18710.
def localCycle00301 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 4 2, .triangle 11 1, .triangle 33 1, .corridorLower 5 6]

-- Original cycle efdc67c7949b016a3ccbd935b8274f3a28314932cf0eb2016739b0416f5d9ded; original global index 18715.
def localCycle00302 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 2, .triangle 18 2, .triangle 4 2, .gapLower 6 2, .triangle 32 2, .gapLower 6 0]

-- Original cycle f17dee4a9bfbc16015d1f9e257645dac71596380e347eb7350cac799690e3717; original global index 18831.
def localCycle00303 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 3 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 33 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle f1e952df3a524e8978d1bc6e3052839e3701d78fee64e77953c80eadc026bfb4; original global index 18866.
def localCycle00304 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 4 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .triangle 32 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle f289c06820393b26303f67731cfc14f3e9ad396ecf61c333b17179a6f0c560b0; original global index 18909.
def localCycle00305 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, 0, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .triangle 18 2, .triangle 4 2, .gapLower 6 3, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle f46bc06ce47808e1ecda604b07492dc7fa3a0b3774f63d90d9f4c786ebb3738e; original global index 19055.
def localCycle00306 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 1 6, .distance 4 6, .distance 0 4, .distance 0 2]
    constant := ![2, -2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .gapLower 6 4, .triangle 13 0, .triangle 6 1]

-- Original cycle f5006ecaefebedd333f24fb4f79fcce9e68995aa3ea5f0aa0ce2f55046db9b5b; original global index 19103.
def localCycle00307 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 4 6, .distance 2 6, .distance 2 5]
    constant := ![2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, true] }
  origin := ![.gapUpper 5 5, .triangle 34 2, .gapLower 6 4, .triangle 30 1]

-- Original cycle f57e1e824185699adad088a2f420c4df40f40293cb45208438b2b0e46c4ce02e; original global index 19140.
def localCycle00308 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 4, .distance 4 5, .distance 0 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 22 0, .triangle 12 0, .triangle 9 1, .corridorLower 3 4]

-- Original cycle f5efb39f541d10b671c2c84703f65063f9dd1abb9f92d31aff6d0f8c5eda6bd9; original global index 19191.
def localCycle00309 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .triangle 32 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle f708fb7f614b8d14b1e76b8bbd0bdd731a4d02e21accad97e841397b26906f7c; original global index 19266.
def localCycle00310 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 17 2, .triangle 24 0, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle f860170dd2a27380b2b73beede74fe7f8366f362e7d0c033355c92f90e784d39; original global index 19371.
def localCycle00311 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 4 5, .distance 0 4, .distance 0 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![4, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle f8606832118a8ab03e353c627fa8edf3e20d015f6cdc7072ef105033e674a3ae; original global index 19372.
def localCycle00312 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapLower 6 3, .triangle 14 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle f89edf5c57310fab1b344b2e968282bc5a1ec827ae0a085e409187791dbf2e54; original global index 19391.
def localCycle00313 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 1 6, .distance 4 6, .distance 0 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .triangle 23 1, .gapLower 6 2, .triangle 11 1, .triangle 32 1, .corridorLower 3 4]

-- Original cycle f943b80bcd083cd7252815521f87c0682ae2982e1fb7ebcaee5cb2d2dff7051a; original global index 19439.
def localCycle00314 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 17 2, .triangle 24 0, .triangle 33 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle fafca9ccb25eb5cb6545597d44861d82681ab469e7edcd1069dc620aeeda5613; original global index 19589.
def localCycle00315 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .triangle 11 1, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle fcce7240f92e21ea959e4193b027fe4468e02876d64341d21cf16ce4c37638ff; original global index 19756.
def localCycle00316 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle fd09b58185dfdabdd871899d37dd9239be892c6a95c836efea127ba48e268697; original global index 19775.
def localCycle00317 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 2 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle fda0a3b6b60b2d9a0976f7299e6543a29981e3be6e4cbc8a94d185d3d6aa71fc; original global index 19827.
def localCycle00318 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .triangle 31 1, .corridorLower 3 4]

-- Original cycle fed9ad088b136544ab3066e823e935968d93cbf3557f63204e387744f2d2e38e; original global index 19926.
def localCycle00319 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 5, .triangle 17 2, .triangle 3 2, .triangle 14 2, .gapLower 6 3, .triangle 32 2, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle fef0683aa32bb841e46e1c1fc8cbc3d4caaf1c9abb3042a6291a7abdb7743898; original global index 19932.
def localCycle00320 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 28 0, .triangle 16 2, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle ff66d2d9ab223306ee1107403d093a851034faeeb5495c2d5fdc22d0f7da4d63; original global index 19968.
def localCycle00321 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 2, .triangle 21 1, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

def library : Library := fun id => if id < 161 then (if id < 80 then (if id < 40 then (if id < 20 then (if id < 10 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 7 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))))) else (if id < 15 then (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)))) else (if id < 17 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)))))) else (if id < 30 then (if id < 25 then (if id < 22 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))) else (if id < 27 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))))) else (if id < 35 then (if id < 32 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)))) else (if id < 37 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none)) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none))))))) else (if id < 60 then (if id < 50 then (if id < 45 then (if id < 42 then (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none)) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none)))) else (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none))))) else (if id < 55 then (if id < 52 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)))) else (if id < 57 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none)))))) else (if id < 70 then (if id < 65 then (if id < 62 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none)) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)))) else (if id < 67 then (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none))))) else (if id < 75 then (if id < 72 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)))) else (if id < 77 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)))))))) else (if id < 120 then (if id < 100 then (if id < 90 then (if id < 85 then (if id < 82 then (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none)) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none)))) else (if id < 87 then (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none))))) else (if id < 95 then (if id < 92 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)))) else (if id < 97 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none)))))) else (if id < 110 then (if id < 105 then (if id < 102 then (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)))) else (if id < 107 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none))))) else (if id < 115 then (if id < 112 then (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none)) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none)))) else (if id < 117 then (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none))))))) else (if id < 140 then (if id < 130 then (if id < 125 then (if id < 122 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)))) else (if id < 127 then (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none)) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none))))) else (if id < 135 then (if id < 132 then (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none)) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)))) else (if id < 137 then (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)))))) else (if id < 150 then (if id < 145 then (if id < 142 then (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none)) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none)))) else (if id < 147 then (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none)) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none))))) else (if id < 155 then (if id < 152 then (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none)) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none)))) else (if id < 158 then (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none))) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none))))))))) else (if id < 241 then (if id < 201 then (if id < 181 then (if id < 171 then (if id < 166 then (if id < 163 then (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none)) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none)))) else (if id < 168 then (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none)) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none))))) else (if id < 176 then (if id < 173 then (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none)) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id = 175 then some localCycle00175 else none)))) else (if id < 178 then (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none)) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none)))))) else (if id < 191 then (if id < 186 then (if id < 183 then (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none)) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id = 185 then some localCycle00185 else none)))) else (if id < 188 then (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id = 187 then some localCycle00187 else none)) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none))))) else (if id < 196 then (if id < 193 then (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none)) else (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none)))) else (if id < 198 then (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none)) else (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id = 200 then some localCycle00200 else none))))))) else (if id < 221 then (if id < 211 then (if id < 206 then (if id < 203 then (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none)) else (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none)))) else (if id < 208 then (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none)) else (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id = 210 then some localCycle00210 else none))))) else (if id < 216 then (if id < 213 then (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id = 212 then some localCycle00212 else none)) else (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none)))) else (if id < 218 then (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id = 217 then some localCycle00217 else none)) else (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id = 220 then some localCycle00220 else none)))))) else (if id < 231 then (if id < 226 then (if id < 223 then (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id = 222 then some localCycle00222 else none)) else (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id = 225 then some localCycle00225 else none)))) else (if id < 228 then (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id = 227 then some localCycle00227 else none)) else (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id = 230 then some localCycle00230 else none))))) else (if id < 236 then (if id < 233 then (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id = 232 then some localCycle00232 else none)) else (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id < 235 then (if id = 234 then some localCycle00234 else none) else (if id = 235 then some localCycle00235 else none)))) else (if id < 238 then (if id < 237 then (if id = 236 then some localCycle00236 else none) else (if id = 237 then some localCycle00237 else none)) else (if id < 239 then (if id = 238 then some localCycle00238 else none) else (if id < 240 then (if id = 239 then some localCycle00239 else none) else (if id = 240 then some localCycle00240 else none)))))))) else (if id < 281 then (if id < 261 then (if id < 251 then (if id < 246 then (if id < 243 then (if id < 242 then (if id = 241 then some localCycle00241 else none) else (if id = 242 then some localCycle00242 else none)) else (if id < 244 then (if id = 243 then some localCycle00243 else none) else (if id < 245 then (if id = 244 then some localCycle00244 else none) else (if id = 245 then some localCycle00245 else none)))) else (if id < 248 then (if id < 247 then (if id = 246 then some localCycle00246 else none) else (if id = 247 then some localCycle00247 else none)) else (if id < 249 then (if id = 248 then some localCycle00248 else none) else (if id < 250 then (if id = 249 then some localCycle00249 else none) else (if id = 250 then some localCycle00250 else none))))) else (if id < 256 then (if id < 253 then (if id < 252 then (if id = 251 then some localCycle00251 else none) else (if id = 252 then some localCycle00252 else none)) else (if id < 254 then (if id = 253 then some localCycle00253 else none) else (if id < 255 then (if id = 254 then some localCycle00254 else none) else (if id = 255 then some localCycle00255 else none)))) else (if id < 258 then (if id < 257 then (if id = 256 then some localCycle00256 else none) else (if id = 257 then some localCycle00257 else none)) else (if id < 259 then (if id = 258 then some localCycle00258 else none) else (if id < 260 then (if id = 259 then some localCycle00259 else none) else (if id = 260 then some localCycle00260 else none)))))) else (if id < 271 then (if id < 266 then (if id < 263 then (if id < 262 then (if id = 261 then some localCycle00261 else none) else (if id = 262 then some localCycle00262 else none)) else (if id < 264 then (if id = 263 then some localCycle00263 else none) else (if id < 265 then (if id = 264 then some localCycle00264 else none) else (if id = 265 then some localCycle00265 else none)))) else (if id < 268 then (if id < 267 then (if id = 266 then some localCycle00266 else none) else (if id = 267 then some localCycle00267 else none)) else (if id < 269 then (if id = 268 then some localCycle00268 else none) else (if id < 270 then (if id = 269 then some localCycle00269 else none) else (if id = 270 then some localCycle00270 else none))))) else (if id < 276 then (if id < 273 then (if id < 272 then (if id = 271 then some localCycle00271 else none) else (if id = 272 then some localCycle00272 else none)) else (if id < 274 then (if id = 273 then some localCycle00273 else none) else (if id < 275 then (if id = 274 then some localCycle00274 else none) else (if id = 275 then some localCycle00275 else none)))) else (if id < 278 then (if id < 277 then (if id = 276 then some localCycle00276 else none) else (if id = 277 then some localCycle00277 else none)) else (if id < 279 then (if id = 278 then some localCycle00278 else none) else (if id < 280 then (if id = 279 then some localCycle00279 else none) else (if id = 280 then some localCycle00280 else none))))))) else (if id < 301 then (if id < 291 then (if id < 286 then (if id < 283 then (if id < 282 then (if id = 281 then some localCycle00281 else none) else (if id = 282 then some localCycle00282 else none)) else (if id < 284 then (if id = 283 then some localCycle00283 else none) else (if id < 285 then (if id = 284 then some localCycle00284 else none) else (if id = 285 then some localCycle00285 else none)))) else (if id < 288 then (if id < 287 then (if id = 286 then some localCycle00286 else none) else (if id = 287 then some localCycle00287 else none)) else (if id < 289 then (if id = 288 then some localCycle00288 else none) else (if id < 290 then (if id = 289 then some localCycle00289 else none) else (if id = 290 then some localCycle00290 else none))))) else (if id < 296 then (if id < 293 then (if id < 292 then (if id = 291 then some localCycle00291 else none) else (if id = 292 then some localCycle00292 else none)) else (if id < 294 then (if id = 293 then some localCycle00293 else none) else (if id < 295 then (if id = 294 then some localCycle00294 else none) else (if id = 295 then some localCycle00295 else none)))) else (if id < 298 then (if id < 297 then (if id = 296 then some localCycle00296 else none) else (if id = 297 then some localCycle00297 else none)) else (if id < 299 then (if id = 298 then some localCycle00298 else none) else (if id < 300 then (if id = 299 then some localCycle00299 else none) else (if id = 300 then some localCycle00300 else none)))))) else (if id < 311 then (if id < 306 then (if id < 303 then (if id < 302 then (if id = 301 then some localCycle00301 else none) else (if id = 302 then some localCycle00302 else none)) else (if id < 304 then (if id = 303 then some localCycle00303 else none) else (if id < 305 then (if id = 304 then some localCycle00304 else none) else (if id = 305 then some localCycle00305 else none)))) else (if id < 308 then (if id < 307 then (if id = 306 then some localCycle00306 else none) else (if id = 307 then some localCycle00307 else none)) else (if id < 309 then (if id = 308 then some localCycle00308 else none) else (if id < 310 then (if id = 309 then some localCycle00309 else none) else (if id = 310 then some localCycle00310 else none))))) else (if id < 316 then (if id < 313 then (if id < 312 then (if id = 311 then some localCycle00311 else none) else (if id = 312 then some localCycle00312 else none)) else (if id < 314 then (if id = 313 then some localCycle00313 else none) else (if id < 315 then (if id = 314 then some localCycle00314 else none) else (if id = 315 then some localCycle00315 else none)))) else (if id < 319 then (if id < 317 then (if id = 316 then some localCycle00316 else none) else (if id < 318 then (if id = 317 then some localCycle00317 else none) else (if id = 318 then some localCycle00318 else none))) else (if id < 320 then (if id = 319 then some localCycle00319 else none) else (if id < 321 then (if id = 320 then some localCycle00320 else none) else (if id = 321 then some localCycle00321 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 4, 5, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 0, 1, 2, 6, 5], ![3, 0, 1, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 8 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13440)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 4, 5, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 1, 2, 5, 6], ![3, 0, 1, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 52 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13441)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 4, 5, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 1, 2, 6, 5], ![3, 0, 1, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 52 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13442)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 4, 6, 5, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 1, 2, 6, 5], ![3, 0, 1, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 114 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13443)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 6, 4, 5, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 1, 6, 2, 5], ![3, 0, 1, 6, 2, 4], ![0, 1, 3, 5, 4, 2]], proof := .tail 228 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13444)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 6, 3], ![1, 0, 4, 5, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 2, 5, 6], ![3, 0, 1, 2, 4, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 320 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13445)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 6, 3], ![1, 0, 4, 5, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 2, 6, 5], ![3, 0, 1, 2, 6, 4], ![0, 3, 1, 2, 5, 4]], proof := .tail 8 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13446)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 6, 3], ![1, 0, 4, 6, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 2, 6, 5], ![3, 0, 1, 6, 2, 4], ![0, 3, 1, 5, 2, 4]], proof := .tail 114 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13447)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 6, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 6, 2, 5], ![3, 0, 1, 6, 2, 4], ![0, 3, 1, 5, 4, 2]], proof := .tail 299 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13448)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 6, 5, 3], ![1, 0, 4, 6, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 2, 6, 5], ![3, 0, 6, 1, 2, 4], ![0, 3, 5, 1, 2, 4]], proof := .tail 243 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13449)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 6, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 6, 2, 5], ![3, 0, 6, 1, 2, 4], ![0, 3, 5, 1, 4, 2]], proof := .tail 299 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13450)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 6, 1, 2, 5], ![3, 0, 6, 1, 2, 4], ![0, 3, 5, 4, 1, 2]], proof := .tail 83 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13451)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 4, 5, 6, 3], ![1, 0, 4, 5, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 2, 5, 6], ![3, 0, 1, 2, 4, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 320 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13452)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 4, 5, 6, 3], ![1, 0, 4, 5, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 2, 6, 5], ![3, 0, 1, 2, 6, 4], ![3, 0, 1, 2, 5, 4]], proof := .tail 8 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13453)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 4, 5, 6, 3], ![1, 0, 4, 6, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 2, 6, 5], ![3, 0, 1, 6, 2, 4], ![3, 0, 1, 5, 2, 4]], proof := .tail 0 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13454)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 4, 6, 5, 3], ![1, 0, 4, 6, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 2, 6, 5], ![3, 0, 6, 1, 2, 4], ![3, 0, 5, 1, 2, 4]], proof := .low6 (![314, 265, 122, 255, 186, 16, 258, 310, 154, 31, 170, 28, 178, 147, 11, 217, 191, 54, 58, 200, 190, 221, 209, 235, 39, 239, 289, 30]) }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13455)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![2, 1, 4, 6, 5, 3], ![2, 0, 4, 6, 5, 3], ![1, 0, 4, 6, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 2, 6, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 0, 1, 2, 4]], proof := .low6 (![253, 293, 298, 149, 203, 16, 258, 77, 84, 194, 172, 276, 178, 211, 118, 118, 118, 118, 36, 130, 230, 282, 144, 136, 312, 76, 289, 30]) }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13456)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![2, 1, 4, 6, 5, 3], ![2, 0, 4, 6, 5, 3], ![1, 0, 4, 6, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 1, 2, 6, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 0, 1, 2, 4]], proof := .low6 (![104, 220, 19, 51, 143, 16, 258, 10, 125, 315, 185, 184, 288, 15, 284, 57, 233, 54, 316, 99, 165, 178, 141, 278, 115, 301, 289, 30]) }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13457)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 4, 5, 6, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 6, 2, 5], ![3, 0, 1, 6, 2, 4], ![3, 0, 1, 5, 4, 2]], proof := .tail 65 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13458)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 4, 6, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 6, 2, 5], ![3, 0, 6, 1, 2, 4], ![3, 0, 5, 1, 4, 2]], proof := .tail 219 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13459)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![2, 1, 4, 6, 5, 3], ![2, 0, 4, 6, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 6, 2, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 0, 1, 4, 2]], proof := .tail 219 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13460)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![2, 1, 4, 6, 5, 3], ![2, 0, 4, 6, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 1, 6, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 0, 1, 4, 2]], proof := .tail 219 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13461)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 1, 2, 5], ![3, 0, 6, 1, 2, 4], ![3, 0, 5, 4, 1, 2]], proof := .tail 101 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13462)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![2, 1, 4, 6, 5, 3], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 1, 2, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 0, 4, 1, 2]], proof := .tail 317 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13463)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![2, 1, 4, 6, 5, 3], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 6, 1, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 0, 4, 1, 2]], proof := .tail 317 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13464)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![2, 1, 6, 4, 5, 3], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 1, 2, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 4, 0, 1, 2]], proof := .low6 (![180, 119, 290, 156, 87, 187, 71, 131, 285, 304, 73, 73, 73, 300, 201, 177, 177, 177, 88, 281, 281, 281, 18, 267, 252, 231, 49, 6]) }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13465)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![2, 1, 6, 4, 5, 3], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 4, 0, 1, 2]], proof := .low6 (![216, 22, 55, 156, 87, 187, 71, 61, 264, 160, 74, 74, 74, 27, 309, 151, 269, 93, 106, 236, 226, 95, 18, 267, 252, 231, 148, 6]) }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13466)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![2, 1, 6, 4, 5, 3], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 4, 3, 0, 1, 2]], proof := .low6 (![169, 166, 171, 305, 87, 187, 71, 40, 173, 96, 107, 150, 85, 291, 295, 50, 261, 7, 311, 175, 153, 273, 48, 41, 63, 231, 262, 6]) }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13467)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![2, 6, 1, 4, 5, 3], ![2, 6, 0, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 1, 2, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 4, 1, 0, 2]], proof := .tail 256 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13468)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![2, 6, 1, 4, 5, 3], ![2, 6, 0, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 4, 1, 0, 2]], proof := .tail 152 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13469)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![2, 6, 1, 4, 5, 3], ![2, 6, 0, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 212 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13470)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![2, 6, 0, 4, 5, 3], ![1, 6, 0, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 1, 2, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 4, 1, 2, 0]], proof := .tail 20 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13471)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![2, 6, 0, 4, 5, 3], ![1, 6, 0, 4, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 4, 1, 2, 0]], proof := .tail 82 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13472)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![2, 6, 0, 4, 5, 3], ![1, 6, 0, 4, 5, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 109 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13473)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![6, 2, 0, 4, 5, 3], ![6, 1, 0, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 1, 2, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 4, 2, 1, 0]], proof := .tail 121 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13474)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![6, 2, 0, 4, 5, 3], ![6, 1, 0, 4, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 121 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13475)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![6, 2, 0, 4, 5, 3], ![6, 1, 0, 4, 5, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 168 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13476)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 5, 4, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 0, 1, 5, 2, 6], ![3, 0, 1, 4, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 254 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13477)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 5, 4, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 1, 5, 2, 6], ![3, 0, 1, 4, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 52 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13478)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 5, 6, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 1, 5, 6, 2], ![3, 0, 1, 4, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 218 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13479)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 1, 5, 6, 2], ![3, 0, 1, 4, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 279 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13480)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 1, 6, 5, 2], ![3, 0, 1, 6, 4, 2], ![0, 1, 3, 5, 4, 2]], proof := .tail 102 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13481)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 6, 3], ![1, 0, 5, 4, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 5, 2, 6], ![3, 0, 1, 4, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 66 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13482)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 6, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 5, 6, 2], ![3, 0, 1, 4, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 218 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13483)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 6, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 5, 6, 2], ![3, 0, 1, 4, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 279 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13484)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 6, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 6, 5, 2], ![3, 0, 1, 6, 4, 2], ![0, 3, 1, 5, 4, 2]], proof := .tail 321 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13485)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 6, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 6, 5, 2], ![3, 0, 6, 1, 4, 2], ![0, 3, 5, 1, 4, 2]], proof := .tail 296 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13486)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 6, 1, 5, 2], ![3, 0, 6, 1, 4, 2], ![0, 3, 5, 4, 1, 2]], proof := .tail 202 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13487)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 4, 5, 6, 3], ![1, 0, 5, 4, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 5, 2, 6], ![3, 0, 1, 4, 2, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 66 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13488)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 4, 5, 6, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 5, 6, 2], ![3, 0, 1, 4, 2, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 234 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13489)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 4, 5, 6, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 5, 6, 2], ![3, 0, 1, 4, 6, 2], ![3, 0, 1, 4, 5, 2]], proof := .tail 279 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13490)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 4, 5, 6, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 6, 5, 2], ![3, 0, 1, 6, 4, 2], ![3, 0, 1, 5, 4, 2]], proof := .tail 162 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13491)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 4, 6, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 6, 5, 2], ![3, 0, 6, 1, 4, 2], ![3, 0, 5, 1, 4, 2]], proof := .tail 182 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13492)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![2, 1, 4, 6, 5, 3], ![2, 0, 4, 6, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 6, 5, 2], ![3, 6, 0, 1, 4, 2], ![3, 5, 0, 1, 4, 2]], proof := .tail 182 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13493)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![2, 1, 4, 6, 5, 3], ![2, 0, 4, 6, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 1, 6, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 3, 0, 1, 4, 2]], proof := .tail 164 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13494)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 1, 5, 2], ![3, 0, 6, 1, 4, 2], ![3, 0, 5, 4, 1, 2]], proof := .tail 222 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13495)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![2, 1, 4, 6, 5, 3], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 1, 5, 2], ![3, 6, 0, 1, 4, 2], ![3, 5, 0, 4, 1, 2]], proof := .tail 222 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13496)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![2, 1, 4, 6, 5, 3], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 6, 1, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 3, 0, 4, 1, 2]], proof := .tail 222 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13497)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![2, 1, 6, 4, 5, 3], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 1, 5, 2], ![3, 6, 0, 1, 4, 2], ![3, 5, 4, 0, 1, 2]], proof := .tail 29 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13498)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![2, 1, 6, 4, 5, 3], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 1, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 3, 4, 0, 1, 2]], proof := .tail 29 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13499)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![2, 1, 6, 4, 5, 3], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 1, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 78 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13500)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![2, 6, 1, 4, 5, 3], ![2, 6, 0, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 1, 5, 2], ![3, 6, 0, 1, 4, 2], ![3, 5, 4, 1, 0, 2]], proof := .tail 142 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13501)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![2, 6, 1, 4, 5, 3], ![2, 6, 0, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 1, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 3, 4, 1, 0, 2]], proof := .tail 142 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13502)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![2, 6, 1, 4, 5, 3], ![2, 6, 0, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 1, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 78 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13503)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![2, 6, 0, 4, 5, 3], ![1, 6, 0, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 1, 5, 2], ![3, 6, 0, 1, 4, 2], ![3, 5, 4, 1, 2, 0]], proof := .tail 142 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13504)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![2, 6, 0, 4, 5, 3], ![1, 6, 0, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 1, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 3, 4, 1, 2, 0]], proof := .tail 142 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13505)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![2, 6, 0, 4, 5, 3], ![1, 6, 0, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 1, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 45 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13506)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![6, 2, 0, 4, 5, 3], ![6, 1, 0, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 1, 5, 2], ![3, 6, 0, 1, 4, 2], ![3, 5, 4, 2, 1, 0]], proof := .tail 167 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13507)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![6, 2, 0, 4, 5, 3], ![6, 1, 0, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 1, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 3, 4, 2, 1, 0]], proof := .tail 167 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13508)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![6, 2, 0, 4, 5, 3], ![6, 1, 0, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 1, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 123 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13509)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 5, 4, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 0, 5, 1, 2, 6], ![3, 0, 4, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 17 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13510)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 5, 4, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 5, 1, 2, 6], ![3, 0, 4, 1, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 277 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13511)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 5, 6, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 5, 1, 6, 2], ![3, 0, 4, 1, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 251 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13512)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 5, 1, 6, 2], ![3, 0, 4, 1, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 161 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13513)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 5, 4, 6, 3], ![1, 0, 5, 4, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 1, 2, 6], ![3, 0, 4, 1, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 208 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13514)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 5, 4, 6, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 1, 6, 2], ![3, 0, 4, 1, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 308 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13515)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 5, 4, 6, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 1, 6, 2], ![3, 0, 4, 1, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 60 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13516)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 1, 2, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 214 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13517)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 5, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 1, 6, 2], ![0, 3, 4, 1, 5, 2]], proof := .tail 161 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13518)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 6, 1, 2], ![0, 3, 4, 5, 1, 2]], proof := .tail 238 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13519)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 6, 5, 1, 2], ![3, 0, 6, 4, 1, 2], ![0, 3, 5, 4, 1, 2]], proof := .tail 275 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13520)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 5, 4, 6, 3], ![1, 0, 5, 4, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 1, 2, 6], ![3, 0, 4, 1, 2, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 208 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13521)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 5, 4, 6, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 1, 6, 2], ![3, 0, 4, 1, 2, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 308 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13522)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 5, 4, 6, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 1, 6, 2], ![3, 0, 4, 1, 6, 2], ![3, 0, 1, 4, 5, 2]], proof := .tail 60 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13523)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 1, 2, 6], ![3, 0, 4, 1, 2, 5]], proof := .low6 (![14, 265, 56, 245, 70, 240, 189, 75, 196, 260, 129, 128, 43, 21, 120, 263, 69, 9, 197, 313, 13, 116, 272, 5, 181, 112, 263, 53]) }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13524)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 5, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 1, 6, 2], ![3, 0, 4, 1, 5, 2]], proof := .tail 60 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13525)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 6, 1, 2], ![3, 0, 4, 5, 1, 2]], proof := .tail 238 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13526)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 5, 1, 2], ![3, 0, 6, 4, 1, 2], ![3, 0, 5, 4, 1, 2]], proof := .tail 318 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13527)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![2, 1, 4, 6, 5, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 5, 1, 2], ![3, 6, 0, 4, 1, 2], ![3, 5, 0, 4, 1, 2]], proof := .tail 110 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13528)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![2, 1, 4, 6, 5, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 6, 5, 1, 2], ![6, 3, 0, 4, 1, 2], ![5, 3, 0, 4, 1, 2]], proof := .low6 (![104, 81, 303, 103, 297, 187, 4, 32, 24, 244, 47, 6, 24, 283, 140, 47, 6, 270, 25, 47, 6, 91, 117, 213, 192, 306, 47, 6]) }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13529)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![2, 1, 6, 4, 5, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 5, 1, 2], ![3, 6, 0, 4, 1, 2], ![3, 5, 4, 0, 1, 2]], proof := .tail 26 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13530)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![2, 1, 6, 4, 5, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 5, 1, 2], ![6, 3, 0, 4, 1, 2], ![5, 3, 4, 0, 1, 2]], proof := .tail 26 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13531)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![2, 1, 6, 4, 5, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 5, 1, 2], ![6, 3, 0, 4, 1, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 198 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13532)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![2, 6, 1, 4, 5, 3], ![2, 6, 0, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 5, 1, 2], ![3, 6, 0, 4, 1, 2], ![3, 5, 4, 1, 0, 2]], proof := .tail 26 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13533)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![2, 6, 1, 4, 5, 3], ![2, 6, 0, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 5, 1, 2], ![6, 3, 0, 4, 1, 2], ![5, 3, 4, 1, 0, 2]], proof := .tail 26 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13534)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![2, 6, 1, 4, 5, 3], ![2, 6, 0, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 5, 1, 2], ![6, 3, 0, 4, 1, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 198 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13535)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![2, 6, 0, 5, 4, 3], ![1, 6, 0, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 5, 1, 2], ![3, 6, 0, 4, 1, 2], ![3, 5, 4, 1, 2, 0]], proof := .tail 26 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13536)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![2, 6, 0, 5, 4, 3], ![1, 6, 0, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 5, 1, 2], ![6, 3, 0, 4, 1, 2], ![5, 3, 4, 1, 2, 0]], proof := .tail 26 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13537)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![2, 6, 0, 5, 4, 3], ![1, 6, 0, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 5, 1, 2], ![6, 3, 0, 4, 1, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 198 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13538)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![6, 2, 0, 5, 4, 3], ![6, 1, 0, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 5, 1, 2], ![3, 6, 0, 4, 1, 2], ![3, 5, 4, 2, 1, 0]], proof := .tail 33 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13539)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![6, 2, 0, 5, 4, 3], ![6, 1, 0, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 5, 1, 2], ![6, 3, 0, 4, 1, 2], ![5, 3, 4, 2, 1, 0]], proof := .tail 33 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13540)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![6, 2, 0, 5, 4, 3], ![6, 1, 0, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 5, 1, 2], ![6, 3, 0, 4, 1, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 34 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13541)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![2, 1, 5, 4, 3, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 5, 4, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 5, 0, 1, 2, 6], ![3, 4, 0, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .low0 (![158, 207, 94, 127, 37, 248, 38, 246, 100, 145, 163, 174, 274, 193, 246, 246, 246, 246, 266, 100, 100, 100, 59, 292, 89, 2, 163, 183]) }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13542)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![2, 1, 5, 4, 3, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 5, 4, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 5, 0, 1, 2, 6], ![3, 4, 0, 1, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 90 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13543)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![2, 1, 5, 4, 3, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 5, 6, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 5, 0, 1, 6, 2], ![3, 4, 0, 1, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 108 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13544)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![2, 1, 5, 4, 3, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 5, 0, 1, 6, 2], ![3, 4, 0, 1, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 161 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13545)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![2, 1, 5, 4, 3, 6], ![2, 0, 5, 4, 6, 3], ![1, 0, 5, 4, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 1, 2, 6], ![3, 4, 0, 1, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 62 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13546)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![2, 1, 5, 4, 3, 6], ![2, 0, 5, 4, 6, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 1, 6, 2], ![3, 4, 0, 1, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 105 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13547)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![2, 1, 5, 4, 3, 6], ![2, 0, 5, 4, 6, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 1, 6, 2], ![3, 4, 0, 1, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 161 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13548)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![2, 1, 5, 4, 3, 6], ![2, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 1, 2, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 92 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13549)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![2, 1, 5, 4, 3, 6], ![2, 0, 5, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 1, 6, 2], ![0, 3, 4, 1, 5, 2]], proof := .tail 161 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13550)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![2, 1, 5, 4, 3, 6], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 6, 1, 2], ![0, 3, 4, 5, 1, 2]], proof := .tail 238 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13551)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![2, 1, 5, 4, 6, 3], ![2, 0, 5, 4, 6, 3], ![1, 0, 5, 4, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 1, 2, 6], ![3, 4, 0, 1, 2, 6], ![3, 0, 1, 2, 4, 5]], proof := .low6 (![237, 265, 135, 286, 204, 46, 247, 224, 138, 68, 205, 242, 124, 210, 126, 307, 242, 159, 229, 1, 242, 138, 225, 242, 68, 79, 12, 242]) }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13552)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![2, 1, 5, 4, 6, 3], ![2, 0, 5, 4, 6, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 1, 6, 2], ![3, 4, 0, 1, 2, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 105 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13553)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![2, 1, 5, 4, 6, 3], ![2, 0, 5, 4, 6, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 1, 6, 2], ![3, 4, 0, 1, 6, 2], ![3, 0, 1, 4, 5, 2]], proof := .tail 161 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13554)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![2, 1, 5, 4, 6, 3], ![2, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 1, 2, 6], ![3, 0, 4, 1, 2, 5]], proof := .tail 92 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13555)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![2, 1, 5, 4, 6, 3], ![2, 0, 5, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 1, 6, 2], ![3, 0, 4, 1, 5, 2]], proof := .tail 161 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13556)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![2, 1, 5, 4, 6, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 6, 1, 2], ![3, 0, 4, 5, 1, 2]], proof := .tail 238 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13557)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![2, 1, 5, 6, 4, 3], ![2, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 0, 1, 2, 6], ![3, 4, 0, 1, 2, 5]], proof := .low6 (![294, 287, 137, 3, 215, 240, 189, 206, 302, 133, 146, 42, 35, 113, 206, 206, 206, 206, 241, 155, 97, 132, 139, 271, 195, 112, 80, 179]) }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13558)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![2, 1, 5, 6, 4, 3], ![2, 0, 5, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 0, 1, 6, 2], ![3, 4, 0, 1, 5, 2]], proof := .tail 161 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13559)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![2, 1, 5, 6, 4, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 0, 6, 1, 2], ![3, 4, 0, 5, 1, 2]], proof := .tail 238 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13560)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![2, 1, 6, 5, 4, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 6, 0, 1, 2], ![3, 4, 5, 0, 1, 2]], proof := .tail 250 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13561)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![2, 1, 6, 5, 4, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 5, 0, 1, 2], ![3, 6, 4, 0, 1, 2], ![3, 5, 4, 0, 1, 2]], proof := .tail 268 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13562)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![2, 1, 6, 5, 4, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 5, 0, 1, 2], ![6, 3, 4, 0, 1, 2], ![5, 3, 4, 0, 1, 2]], proof := .low6 (![104, 86, 55, 259, 87, 187, 71, 176, 134, 319, 44, 6, 257, 249, 199, 111, 6, 227, 157, 188, 6, 280, 98, 23, 72, 231, 223, 6]) }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13563)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![2, 1, 6, 5, 4, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 5, 0, 1, 2], ![6, 3, 4, 0, 1, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 232 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13564)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![2, 6, 1, 5, 4, 3], ![2, 6, 0, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 6, 0, 1, 2], ![3, 4, 5, 1, 0, 2]], proof := .tail 67 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13565)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![2, 6, 1, 5, 4, 3], ![2, 6, 0, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 5, 0, 1, 2], ![3, 6, 4, 0, 1, 2], ![3, 5, 4, 1, 0, 2]], proof := .tail 64 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13566)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![2, 6, 1, 5, 4, 3], ![2, 6, 0, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 5, 0, 1, 2], ![6, 3, 4, 0, 1, 2], ![5, 3, 4, 1, 0, 2]], proof := .tail 64 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13567)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (13440 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 13440 ≤ id.val) (hhigh : id.val < 13568) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 13440)) = true := by
  let j : Fin 128 := ⟨id.val - 13440, by omega⟩
  have hsum : 13440 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (13440 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard105
