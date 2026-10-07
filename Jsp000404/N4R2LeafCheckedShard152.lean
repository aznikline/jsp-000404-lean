import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard152
open N4R2RowDataReplay

-- Original cycle 02ce5556712f78cffb49e1531b8a8709feae565943f2a8dd8ee11790ddb4963e; original global index 222.
def localCycle00000 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 02f625b59ab0912b57985c8267e54f08536a5930c762fa9b95c09caf0999da9d; original global index 239.
def localCycle00001 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 2]
    constant := ![4, -1, -1, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 5 0, .triangle 8 0, .gapLower 6 3, .triangle 21 0, .gapLower 1 1, .gapLower 2 0]

-- Original cycle 04362bf0f760c5169aa8b7b4a69b31484de253f830bb08631cc021c716412b86; original global index 331.
def localCycle00002 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 6, .distance 0 2, .distance 2 4, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 19 0, .triangle 20 0, .corridorLower 3 5]

-- Original cycle 08c8f4fc08795663cfabe362dc94a613838a8b0bcf01f3916d7a994216fa94f0; original global index 705.
def localCycle00003 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 29 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 0a2058072436d8dfe205a75d4f9af6c50c4725dcabec7b1582293f796f379597; original global index 815.
def localCycle00004 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 2, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 0a9bb02173f7427a50e6ebf488c39b8032ab4b9b4927bc7b9f213facd30b1a63; original global index 846.
def localCycle00005 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 0b52ac490f377746be9984be9e691e9c86c28c44f1af163c1ad8170e542db29c; original global index 909.
def localCycle00006 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 10 0, .triangle 33 2, .gapLower 6 2, .triangle 23 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Original cycle 0b78ab904addaf295bf100937f25996c4566d2213cf117958cba84ba1738ac4d; original global index 921.
def localCycle00007 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle 0c7065b0d22ba814789dd5b6d4916989f1753c2c624ed02772179edfd4ce5ebd; original global index 985.
def localCycle00008 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 29 2, .triangle 8 2, .gapLower 6 2, .triangle 21 2, .gapLower 6 0]

-- Original cycle 0c76cefa88b8ad236148f1cbfc10c8bca5ea361acac8b9048cb41ee58a90fe9a; original global index 987.
def localCycle00009 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 12 1, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 0e985345d3e94a3b2f5d06c67d00220f934807403631647147f6f799fb4df3dd; original global index 1151.
def localCycle00010 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 31 0, .triangle 19 0, .triangle 21 0, .corridorLower 3 6]

-- Original cycle 0f51f98169064bdca16fd7129d632dd7b83bacf40563024a7445859568d5682d; original global index 1218.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 28 0, .triangle 34 0, .triangle 33 0, .gapLower 3 2, .corridorLower 3 4]

-- Original cycle 0fe0541437b569ba2450e6dddf9d231e78128a5b7352c5c4e7ae7b91e6b15903; original global index 1266.
def localCycle00012 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 10b127ad9ede624c2522ed1b3b0a07cdae0db4cde3b58972a22eb192a473f5c9; original global index 1339.
def localCycle00013 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 8 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 110674472db641d1e0f586767dc3590c4b6fd60121320b587e8af9c35349fe71; original global index 1362.
def localCycle00014 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 1 2, .triangle 10 0, .triangle 33 0, .triangle 24 2, .gapUpper 1 5]

-- Original cycle 1144efea9a0263179446abb25ffea39dbefe4cb24abfaec433adaae9c2e6f07c; original global index 1372.
def localCycle00015 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 0, .triangle 28 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 115fbe86a5606ae79af63d368e734d2249119a9d391d6f0fa62770d2cc17a4cb; original global index 1384.
def localCycle00016 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 1 6, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .gapLower 6 3, .gapLower 6 2, .triangle 21 1, .gapLower 3 0]

-- Original cycle 14d615b6f914756e2fdcd7f8ed84d64af58baec3c573d4b326f3415fbc70bd99; original global index 1652.
def localCycle00017 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 29 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 14fe781ae35a0d5f2b7f85bd1e9cb5975087555a770580beed9c34c20a75422c; original global index 1663.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 158425e14f1803757b68c96a99eacef2a8debdba2864f133d1ce7ba41d832f94; original global index 1705.
def localCycle00019 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle 1bdb51a2691743bc5ca038765fbabacb57ca8c54d6df00682e943bcb81b7469c; original global index 2154.
def localCycle00020 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 28 0, .triangle 16 0, .triangle 18 0, .triangle 27 1, .corridorLower 3 6]

-- Original cycle 20017ecd38f80482e2665ae0ab1c10362c19b4bc228ae100f42be6c1a431ea2e; original global index 2456.
def localCycle00021 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 0 5, .distance 0 6, .distance 3 6, .distance 1 6, .theta 1]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 10 2, .triangle 14 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 1 6]

-- Original cycle 243be27e013fd6d145e2c84f3ad5a8fa13250ccee6169eb2962f378cc5cacc6a; original global index 2780.
def localCycle00022 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 1 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 27 1, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 26788f88dc66d8061782259edd5b67c8e5980aad6a274bbe0786995e7c6d0a22; original global index 2954.
def localCycle00023 : Cycle where
  length := 4
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .theta 6]
    constant := ![3, -2, 0, -2]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 23 2, .gapLower 6 0]

-- Original cycle 27aef6115c5255b99cbaf200ae3bca10ff3d18d073c407a2ed2c86b4da964369; original global index 3028.
def localCycle00024 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 13 2, .gapLower 6 2, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 2833e1e56d63e7d00016dbacaf61a5b2488a31a69ce8f669673fce5fa0d2a57d; original global index 3078.
def localCycle00025 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 0 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle 2dcbbf1cbdabb38044282bbcd0217b8637301f752c7e9e63f3f6cfbc948bf61e; original global index 3494.
def localCycle00026 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 2e93be7e67bc714bcd09687bd31f18d5b011b3edfc8d668925e3e7edff00833e; original global index 3559.
def localCycle00027 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 6, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle 2f19adb6aa081349a0648e94b4144bab2ad8586e169b1f1b6d9c4511ede40a11; original global index 3599.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 31cf5c45fdbd19fc925dcffdf7a64d3a0ac41525f969caf1fa7218e8af217959; original global index 3806.
def localCycle00029 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 18 2, .triangle 23 1, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 3282a0b7334f769831e758e3395badb3199c7cb2b982fc5299173bfacfec11a6; original global index 3862.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 3 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 27 1, .gapLower 6 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 35a0629bf455283d4d9aa0dc88e5ca05ec177633a406f87d8e0e5dfd13bfc948; original global index 4110.
def localCycle00031 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 3660c49fc60236e231279ff0e0412d549b5ec73e9afdb5f011a7c462fd723653; original global index 4172.
def localCycle00032 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 29 2, .triangle 30 1, .triangle 33 0, .gapLower 3 2, .corridorLower 3 4]

-- Original cycle 393f5dce4c35096d60baa06bd8dfa71374b39ca36f6518231c17a82160d4651c; original global index 4404.
def localCycle00033 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 4 6, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 34 1]

-- Original cycle 3ac734f247e176694af3cb145f533083fd4ee7dca0b4763198ac98c70b615b7f; original global index 4540.
def localCycle00034 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 3daaf86528d7f60fecc402848d919f39a5c01cdc9529167e26f84d1b5849672e; original global index 4776.
def localCycle00035 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 14 0, .triangle 12 1]

-- Original cycle 3e982efde3885d0af6dd38b022bf2731f73370e5935551ab6249942196017183; original global index 4841.
def localCycle00036 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 30 1, .triangle 33 0, .triangle 31 1, .corridorLower 3 4]

-- Original cycle 3f4d39b834421d0fec01c26f27d642571a272cd62f80d47229b494ef757b273b; original global index 4889.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 6, .distance 2 6, .distance 1 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 2, .gapLower 6 3, .triangle 18 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 40164d6b97d0d924c73b4a73762a97b0a54df057e92bb0a7242a06dd70495bec; original global index 4943.
def localCycle00038 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 0 2]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 6 2, .gapUpper 4 4, .gapLower 6 5, .triangle 8 0]

-- Original cycle 4098f1a246e49ab6df9c6ac42426d6a5a45a8f8a5c401d6cf92cf3859a415256; original global index 4994.
def localCycle00039 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 28 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 411b73b9331adc45768973e3b5eef44df2fadb47244e4e7863bf1d031a3e483b; original global index 5025.
def localCycle00040 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 45c0adc710b12deb4aae4ad699e01383b23a2eb97bfa12734d22c47bd170fac1; original global index 5395.
def localCycle00041 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 16 2, .triangle 22 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle 462c61b4b2497300192d4b715886587818637b7ea6b09fcb03c9714eae5ccb7c; original global index 5431.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 0 5, .distance 0 6, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 7 2, .triangle 14 2, .gapLower 6 3, .triangle 21 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 483afca35d22cdefa6d7e96337014cd3a47686cfbbe43ca08f59fa4a9cecd947; original global index 5591.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 5 0, .triangle 8 2, .gapLower 6 4, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 48425e273500a3bd3781e0eacccb54e931a9133cbc21ec8d79f0a8a4ba260414; original global index 5592.
def localCycle00044 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 0 5, .distance 0 6, .distance 3 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 7 2, .triangle 14 2, .gapLower 6 3, .triangle 21 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 4a867dcc245b3afd07acf3b77ef51b2402663e6a46eb99388cce412dc7889b30; original global index 5780.
def localCycle00045 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 4bc7673c58edf8ae5c674efece2744b8cca10be4d2e44f811876d8d81efdb26b; original global index 5880.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 4d85ddda44d45e9d7e3afa7e8c95a16973fe78a532619b259f7709bdbfe55129; original global index 6019.
def localCycle00047 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 17 2, .triangle 22 1, .triangle 23 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 4fb6edf5c20d2771e5c0fe364d38c83cce9d0976bdae39be84d58a6110455a75; original global index 6190.
def localCycle00048 : Cycle where
  length := 3
  data := {
    node := ![.theta 5, .distance 5 6, .theta 6, .theta 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 0, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5086efcc5be511cd1ae105851c13c079535c1d3a6d950bdad7b3cb9ef0df2581; original global index 6252.
def localCycle00049 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 2 6, .distance 0 6, .distance 0 4]
    constant := ![2, -3, 0, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 8 2, .triangle 13 1]

-- Original cycle 50c9e5f343ac77a5f4e6a9e35be2069cc0d6843b190732de605cc64389cd6fdf; original global index 6274.
def localCycle00050 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 0 6, .distance 0 2]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .triangle 8 1]

-- Original cycle 5566737a8e0ee8e74e0a799ce2aad2fdfccf5034fe6c47a11b4f772e40ef53c0; original global index 6614.
def localCycle00051 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 28 0, .triangle 31 0, .triangle 32 0, .gapLower 4 0, .thetaNext 3]

-- Original cycle 57c15d267e336b67d1d8f2d2c68d5415ab7d10a863b6e75ab5999fd300f81576; original global index 6813.
def localCycle00052 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 587464bcb96d2f377fb931fba6fd72cf9c2a3a86e7861b8b186984e5b71dbe1b; original global index 6863.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 59f5a89ee7bb3ab39c7a0b5843723124d0efc296689114bf451d61e1682b7abf; original global index 7003.
def localCycle00054 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 8 1, .triangle 18 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5a1f3b0006ca53e96b1bde0e7535e3d6034cc15d885d338d69f1a77eb308a560; original global index 7014.
def localCycle00055 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 3 5, .distance 1 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 31 2, .triangle 20 0, .triangle 21 0, .corridorLower 3 6]

-- Original cycle 5a33ea8e4169f4655eb8908d0a717d11f02f36bf35f4fa1eebe8f7f13c1ceb66; original global index 7020.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 2, .triangle 13 1, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 5a6af407e6a59b709cf750b9f7c383aa9ba9b2dcc8a810cd71d5ea0d181f267f; original global index 7038.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 6, .theta 6, .distance 5 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -2, 3, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, -1, 0]
    strict := ![false, false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 18 2, .gapLower 6 0, .corridorUpper 5 6, .gapLower 6 5, .gapUpper 4 6, .thetaNext 3]

-- Original cycle 5b6d61924d1316d83cdd5a88952a816e828a385712c64db75c84f1270c760fd8; original global index 7114.
def localCycle00058 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 29 2, .gapLower 6 3, .triangle 8 1, .triangle 7 0, .triangle 28 1, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 5bf8ec6a7d73975c7b028323436fc95e69e5f14d01565ffb870baf11d014c398; original global index 7156.
def localCycle00059 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 8 1, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 6045daf2aece339eb90e26cd6392379bf53f316390c35f83a3d9bde208bf1230; original global index 7498.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 2 6, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 7 0, .triangle 8 2, .gapLower 6 4, .triangle 27 1, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 62af96468f5187272a5d544994957d2bd03f479085e6981a79106acedff66d2d; original global index 7701.
def localCycle00061 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -3, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 1 2, .triangle 11 0, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle 6301eac9d9b0186bd2c8ca4dc228b73375c28a41e37b669226fad47e9eecb43a; original global index 7719.
def localCycle00062 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 6478e2760caff2620f6cb27f0a87b771e3b769b4e803e690e4d1cee818be046c; original global index 7826.
def localCycle00063 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 5 1, .triangle 7 0, .triangle 28 1, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 684d89d983929da9042a6b9fb656b39db3d8683796852b8bdef234615e8eecbc; original global index 8114.
def localCycle00064 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 26 1, .triangle 31 1, .triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 69508ba595bf2ee30d06e18d2d7f692ace968e780b083ed4d34890dc50f137a9; original global index 8192.
def localCycle00065 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 69fcd76e7875ae52af4a65a869e5269899779f3365dbc6fae52da9cbcffd48b5; original global index 8250.
def localCycle00066 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 28 0, .triangle 31 0, .triangle 32 2, .gapLower 3 1, .gapLower 3 0]

-- Original cycle 6bd9749ebf0ff8fab64ac1ce1621db8cce23eca7f54dde38f4267ce2637fde70; original global index 8400.
def localCycle00067 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 27 1, .corridorLower 3 6]

-- Original cycle 6cd4be0e65fafb9595b7d3a54feda515b7ae3741b328123e98a8c267aa64367e; original global index 8468.
def localCycle00068 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 6df5272ec11c5631aec4cc6750d9a80532350bb9af474514c5bf45741c2dcdeb; original global index 8540.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 26 1, .triangle 31 1, .triangle 32 0, .triangle 23 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 6f1185f36dba5f100d646382231c2ca373d3a492569585cf43c2e956f4b983e7; original global index 8613.
def localCycle00070 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 6f3126c580b717fbcfa43657234b202b10b95407fa2eee32d249b4c762906f29; original global index 8620.
def localCycle00071 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 6, .distance 3 6, .distance 0 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 11 2, .gapLower 6 2, .gapUpper 3 4]

-- Original cycle 6faf0dd4ee030b1d584ecd51c0bb53b767ea3a927a3dc01c43e9e981a7f85ae5; original global index 8664.
def localCycle00072 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 19 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Original cycle 6febeb03d646f7dfdab20d1d7f9912b152191c8f91b86452f0fe99b80fcab020; original global index 8677.
def localCycle00073 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 737b1ebbd19108a4f6d52d2fa9661cde26b1c2b095a9893c63193c33d1088aa6; original global index 8951.
def localCycle00074 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 6, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, -2, 2, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 18 2, .gapLower 6 0, .gapLower 6 6, .triangle 34 0, .triangle 31 0, .triangle 19 0, .gapLower 3 0]

-- Original cycle 73a3591c8d15cf1fa43c3733fd202d49682aa3c0515bad47b602084771947b63; original global index 8965.
def localCycle00075 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 11 1, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 742640b36b5a0e014dc96070fbac9503c0d1f025c253ef6029db060ee5f9d048; original global index 9011.
def localCycle00076 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 1 2, .triangle 11 0, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle 746f148abcd1be7105fb250fabc27fa53179d5e61a50dbc02868df2b33b605ce; original global index 9026.
def localCycle00077 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 32 0, .triangle 23 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 77f09a1e43ee314d43e1198486037e4869430e68f5d7f6378042d6a2c25a62b9; original global index 9276.
def localCycle00078 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 34 0, .triangle 33 0, .gapLower 3 2, .corridorLower 3 4]

-- Original cycle 79b1416834dc2897028903e9cd394218e59533b882c59670c5840b2c5d0498f3; original global index 9414.
def localCycle00079 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -1, 0, -2, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true] }
  origin := ![.triangle 1 2, .triangle 5 1, .triangle 8 0, .triangle 27 1, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle 7a281734ed9258f29f5e7f368c4599800576404d54386d48afbf8435123ed54b; original global index 9446.
def localCycle00080 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 28 1, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 7ad06453d8fed01ef25cbfbfa14c04b7d55ff753c331ad8885fa42d33ff4194c; original global index 9508.
def localCycle00081 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 7b1fca13b04b2371305f51287bcf88e99701a6f930ead72fc4866fc8645574ff; original global index 9536.
def localCycle00082 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 7d115ffd37f5befffc6c741d06aeb35e4ee80610d32cd4c6ece70a51ab3cc35f; original global index 9685.
def localCycle00083 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 7e5d957ad83f3c6f02f128e1b2635929dd11d7d36129e51e1e41c4fc6fffc1b1; original global index 9815.
def localCycle00084 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 0 6, .distance 0 2]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 4, .gapLower 6 3, .triangle 8 1]

-- Original cycle 7f89eff166723350acc23a3e9a1ce9b8f12e37cccc3e3b834b9156aba447a524; original global index 9892.
def localCycle00085 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 6, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle 802677a34c48a1bf182622f02d232376f7c933b85f58866321128b99ca65bb7c; original global index 9941.
def localCycle00086 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 2, .triangle 22 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 80ae8c00e2407fb7aeac6069884d3756586f79cb7432b21fd1a53f3a9a615438; original global index 9992.
def localCycle00087 : Cycle where
  length := 15
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5, .distance 5 6, .theta 6, .theta 5, .distance 4 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -2, 0, 3, 0, 0, -2, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 10 0, .triangle 20 2, .triangle 24 0, .gapLower 6 0, .thetaNext 5, .corridorUpper 4 5, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 8 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2]

-- Original cycle 80dd20ecf1f9a8428e81285ce1afdcd98a02ea17a213261f72affc01bd52e84c; original global index 10002.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 2 4, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 28 1, .triangle 16 0, .triangle 18 0, .triangle 27 1, .corridorLower 3 6]

-- Original cycle 81400eb64a1cce0202f09457f56cf059d388630d7b3a1cbe1bb8df77c3d47766; original global index 10032.
def localCycle00089 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 8 1, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 836178bee1e776e8045a656f64933e8ad3915f360c4855d6aa5d0b48ee5fca55; original global index 10188.
def localCycle00090 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 2 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 7 0, .triangle 8 2, .gapLower 6 4, .triangle 18 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 8367b859461a51444d3095067c7a8c20e0cf34cc105a84a3d198c0a93f4b4eb9; original global index 10192.
def localCycle00091 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 838a62479f137205a57316ff5cad30eb5fe9613ad41a8b571949bc206422cb33; original global index 10208.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 8 1, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 854a5a74e899b52cbf9cc5574edb2b8b4ee6c010e6b4f5ecae7110c1dd3a4785; original global index 10340.
def localCycle00093 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .theta 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -2, 2, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 21 2, .gapLower 6 0, .gapLower 6 6, .triangle 34 0, .triangle 28 0, .triangle 16 0, .corridorLower 1 2]

-- Original cycle 86922ea9a54eb0991067ce3ddf529cfd4015f213d9761e51409edd167ec0493a; original global index 10433.
def localCycle00094 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 871d432ff5891fa6d66753f1a46e998d962c6358d206d022a5eb458930ae6a2b; original global index 10483.
def localCycle00095 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 29 1, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 887af19ac1142be001223105961ad0265e8c6d5caba1659aecd2f7e8e4e937ee; original global index 10575.
def localCycle00096 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 6, .distance 5 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 10 0, .triangle 20 2, .triangle 24 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 8a0658f0b58a81b63e8700c478fbcd72106a9c654bf03a7b75d5b947108d36de; original global index 10698.
def localCycle00097 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 2 6, .distance 0 6, .distance 0 4]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 13 1]

-- Original cycle 8c19ac0f7a53a783e401561a04a5990784f74b9f3f9fbb8a2bc5b357a93b09f8; original global index 10845.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 32 0, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 8ffa8356c952b2d57da1176d740527f60088094a1d8a343b6366f86961852b2f; original global index 11145.
def localCycle00099 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 28 1, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 9160051ac23ce5af682b92db1d1e0aca40c249d19acaeacaae7e42b28024ea18; original global index 11260.
def localCycle00100 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 918859d72e79bebb74206530d63c7e526aecaeb3881a79b429fb992230a2b856; original global index 11271.
def localCycle00101 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -2, 3, 0, -2, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 21 2, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 16 0, .corridorLower 1 2]

-- Original cycle 9218d4cf5d46d082700dab4f2c5d4603a879c6c79e0a3d990d6dfaef85a53298; original global index 11317.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 92cdbcf29a579b3a852e26c47905ea0051a2682acea13c3b907993be5f679055; original global index 11376.
def localCycle00103 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle 97b8b98b686682ef2120da5c0aec76eb32192480523a861cbffdfe1bd612f306; original global index 11783.
def localCycle00104 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 3, .triangle 8 1, .triangle 7 0, .triangle 28 1, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 9af010b15321b9dd3c05c4969393e88810bab4a349f0e2e4564e1662c6a87d87; original global index 12043.
def localCycle00105 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 8 1, .triangle 7 0, .triangle 28 1, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 9b8ea0cd6803deadd26d5505b6220419a783b9774938501bb41d2620f5f76c41; original global index 12098.
def localCycle00106 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5, .distance 5 6, .theta 6, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -2, 2, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 10 0, .triangle 20 2, .triangle 24 0, .gapLower 6 0, .gapLower 6 6, .triangle 29 2, .triangle 8 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2]

-- Original cycle 9e89b6bc350b7a3ed332330471c6a22217d879d1208d818c0a02254919bb14b8; original global index 12348.
def localCycle00107 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 11 1, .triangle 21 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 9eec71c5b7b3bdc420e91be584d927020deecf7659c5832fb06d240f74a6b4f6; original global index 12375.
def localCycle00108 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 5 0, .triangle 8 2, .gapLower 6 3, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 9faedd1d54c69e9a39f6d4c73b3aa19ae52fc26a90440ae50592d2f43549d96a; original global index 12428.
def localCycle00109 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 30 0, .triangle 33 0, .gapLower 3 2, .corridorLower 3 4]

-- Original cycle 9fb613bb5fbd61cedff9c4c41f2887e057d56ac6f77a2c05217b03a51dce2f6e; original global index 12430.
def localCycle00110 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle a223d1c16255e2c994c95970b94f3fc8701de29132fb39f1b418a5906e5c34fb; original global index 12615.
def localCycle00111 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 0, .triangle 16 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle a3e345a5f26563542ce38fa3a0c46cf424d6277bd3c9d99de95d5600cc46013b; original global index 12744.
def localCycle00112 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 19 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle a57204470cca55f3b228ec988d5a7c412154b6540df39131d6a29410ba67df0b; original global index 12856.
def localCycle00113 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 18 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle a5cdd559679336a21601ef21bd80265c57383499e9d6b446b6e1a2ccef8f0f30; original global index 12879.
def localCycle00114 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .corridorLower 4 6, .thetaNext 3]

-- Original cycle a6881044e6c704aef4d9d83d360e39bf7f5e838028db9a29a7b97e0fbe1645e5; original global index 12936.
def localCycle00115 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle a8a4fa15e41495e5131f0f293f0b3fbf886165326fb5fffa0c316c4a157ddb31; original global index 13121.
def localCycle00116 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 2]
    constant := ![4, -1, 0, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .gapLower 3 1, .gapLower 1 1, .gapLower 2 0]

-- Original cycle acc80d37bdd9b8e01ef696baabe3ed6e17191594f3e71e30d6ca856c957df4d7; original global index 13469.
def localCycle00117 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -1, 0, -3, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true] }
  origin := ![.triangle 1 2, .triangle 5 1, .triangle 8 0, .triangle 27 1, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle acfab6aa2f1fc93540fed621b66deb7da26097b3d9306079430f4c6401c8f379; original global index 13482.
def localCycle00118 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle ad0b31f83c1e7b5df89240b87543635c350d3f55a02a3874639c342e62b15c86; original global index 13488.
def localCycle00119 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle ad0cb0d4cc70c39d8d005692e27c3556a18a6fef2952a74e84131317a0a05685; original global index 13490.
def localCycle00120 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 14 2, .gapLower 6 2, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle af9f317d5f7d190ad6b73e79648cb8a7ab09df7052ab5259babd47ebd1cbbd2d; original global index 13718.
def localCycle00121 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle b372728562bc5564a2e13d2a002e6355b02c82a80aa702b7af59ca8b119882b3; original global index 14024.
def localCycle00122 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 2, .triangle 23 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle b4615b60113cbb998deacd373f28e9f5478200630c1e8580f115fa1bad5077af; original global index 14092.
def localCycle00123 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 6, .distance 0 6, .distance 3 6, .theta 3]
    constant := ![3, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle b4e008cf3735cc7e29df6f98cb36047ca123b900146de4197e8861cdb9a85ac4; original global index 14126.
def localCycle00124 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 1 6, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 27 1, .gapLower 6 2, .triangle 21 1, .gapLower 3 0]

-- Original cycle b51b7aabb5004cc45ad34414b9dfcc5aaf33a00632bdbc7d9a886b4dd778b0f4; original global index 14150.
def localCycle00125 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -3, 3, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 21 2, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 29 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 16 0, .corridorLower 1 2]

-- Original cycle b62b42a59d67599f287d8fa14a888d82595685b0d3f027a1a0281ea2a1f2ec83; original global index 14229.
def localCycle00126 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 3 6, .distance 0 3, .distance 0 2]
    constant := ![-1, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.triangle 8 0, .gapLower 6 2, .gapUpper 3 4, .triangle 5 1]

-- Original cycle b7460fb2ab1a3c265c730375cd0ba469cd385b043c35225282d61399eaaca17a; original global index 14307.
def localCycle00127 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 1 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 19 0, .triangle 21 0, .corridorLower 3 6]

-- Original cycle b9951032a1dec5fea3f5f04ed8cee6f494776f33e7cb8e1bf06812114193690d; original global index 14482.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 3 6, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 32 2, .triangle 21 0, .triangle 20 0, .corridorLower 3 5]

-- Original cycle bb351d7cae1391b3f3655a05988514cdaa629f48af003907a6936a97b43a6db6; original global index 14617.
def localCycle00129 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4]

-- Original cycle bc09a6c1c2b4239ced7809693e8bbced607452f78cb248e3a2ebf2417384fa8a; original global index 14683.
def localCycle00130 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .triangle 19 0, .triangle 20 0, .corridorLower 3 5]

-- Original cycle be56c2ff952c4a1246779eb3abcbfe04bd88a9380321a3c91353f3a1f8881053; original global index 14851.
def localCycle00131 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 10 0, .triangle 33 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle bea26689189aad637fa51c9188626217c5b566f9b9e7397e48cd4c5e2104ed22; original global index 14870.
def localCycle00132 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 28 0, .triangle 31 0, .gapLower 3 2, .triangle 21 0, .gapLower 3 0]

-- Original cycle c057a320b7ba0cda0f065143e38e4288acafc2542332052ba3809c3876ae5344; original global index 15013.
def localCycle00133 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4]

-- Original cycle c187371c8b5a0569f6bd73f5e9014194766667b03bfe4e5c4b37284a93601c62; original global index 15115.
def localCycle00134 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle c23faf70872569328b863dc50fd12c992cddbaed4cf8ca0402bc3210b964abb4; original global index 15168.
def localCycle00135 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle c380a57a89469cc0b0dfbc87a47cb666b27f139248cbe770fadefea91aea5886; original global index 15257.
def localCycle00136 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 8 2, .gapLower 6 4, .gapUpper 2 3]

-- Original cycle c5173e68bf4b1ce8910ca1a51455738d47e5ab390bd63bb434acf9aaa335e23d; original global index 15378.
def localCycle00137 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .gapLower 6 3, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c60faa0d9d01e952cbc17b216106cb45009a9fc2c92f0bc0e70459bb2603089e; original global index 15447.
def localCycle00138 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 28 1, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle c929e639d176046fb018f3deae36209d671eec1e1c667b4d3b6f4d4a3fd91b89; original global index 15720.
def localCycle00139 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 8 2, .gapLower 6 3, .gapUpper 2 4]

-- Original cycle c9319e55c3476d58b73fe1ce457134ffc07d7216e40774fc9e44c731ea3c39df; original global index 15723.
def localCycle00140 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 1 6, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 27 1, .gapLower 6 2, .triangle 21 1, .gapLower 3 0]

-- Original cycle c943977423f451a4034205cd6f5506703a98948ffdeb0f0532d1c92215eeef8e; original global index 15734.
def localCycle00141 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 2 6, .distance 1 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 8 1, .triangle 18 2, .gapLower 6 0]

-- Original cycle c9ace21e1441aad2382419a9e631b472e22ca4bab1b0b0f7f08cdd303b6ab9ed; original global index 15766.
def localCycle00142 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 29 0, .triangle 32 0, .gapLower 3 2, .triangle 20 0, .corridorLower 3 5]

-- Original cycle ca8a061bbed47eb5c653e74878c9b7064402c1f33f335bb5d3e4fc127689a276; original global index 15829.
def localCycle00143 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 1, .gapUpper 5 1]

-- Original cycle cbad77d8861faadc749222e78f2f750070edea4c7131c648ade3a48c1588103f; original global index 15912.
def localCycle00144 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 26 1, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaLower 1]

-- Original cycle cbba270611a0e13adb79a4d816a66caa0163f9a521b512c6d72407d20f19815b; original global index 15916.
def localCycle00145 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 14 0, .triangle 33 0, .triangle 31 1, .corridorLower 3 4]

-- Original cycle cc296b6fd778bb9fe8253dbc4253748bbf51019d4bbf400b0493e037655fe50d; original global index 15959.
def localCycle00146 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 6, .distance 0 4]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 13 1]

-- Original cycle d0322db29631f5f59d1c2022e2ef779ee4373b21ac17d96b746c39fc047140e4; original global index 16252.
def localCycle00147 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .gapLower 3 2, .corridorLower 3 4]

-- Original cycle d073dfa91f9e9dcb235892f283b348169871311fb4da1494f9a69a81a09f1803; original global index 16273.
def localCycle00148 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle d0cf22faf8bf6c6b3d431b30788a477f44ebe61299713049a7dd4da43bfde4ec; original global index 16301.
def localCycle00149 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 2, .triangle 23 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle d1dba1f011fb8c1bf8c1496cbb2c41b5486c9899cc85954fab681e7ea1780caf; original global index 16378.
def localCycle00150 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .gapLower 4 1, .gapLower 1 2, .gapLower 3 0]

-- Original cycle d4a2e142f35246441794fc8ad9e4a4696ce29e40bf55e02d7e7c1e670ae47b07; original global index 16590.
def localCycle00151 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 32 0, .triangle 19 0, .triangle 20 0, .corridorLower 3 5]

-- Original cycle d89e7430d6b50cac4b5aceed6960339e3e62624bbb1c521e39ae15a818b6edaa; original global index 16908.
def localCycle00152 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 0 5, .distance 0 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -3, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 10 2, .triangle 14 2, .gapLower 6 3, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle d911b210c585e619f36f98df073a88cdcb8e441f9b98628ec218aa1b9dccc5c8; original global index 16957.
def localCycle00153 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 27 1, .gapLower 3 0]

-- Original cycle d95882de83f4a7e6229a9c8d59195d01d135b8c4cb6a92b0c88b8dd9965c75f2; original global index 16987.
def localCycle00154 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 3 6, .distance 0 3, .distance 0 2]
    constant := ![0, -2, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true] }
  origin := ![.triangle 8 2, .gapLower 6 3, .triangle 27 1, .gapUpper 3 4, .triangle 5 1]

-- Original cycle d9fea9eb3f69d235b2493ac02d3d9c94b564777d7ec284f65cd80d7054772bae; original global index 17035.
def localCycle00155 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle dba37705752a49769c117a4f688b12ccf072186c458107e1465bad971fa04246; original global index 17165.
def localCycle00156 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 1 6, .distance 1 5, .theta 5]
    constant := ![3, -1, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 8 1, .gapLower 6 2, .triangle 21 2, .triangle 24 1, .gapLower 5 0]

-- Original cycle dc734927295d77def2fdcf16fe354e0f79461c723aca05018fb7f403ae1862e0; original global index 17228.
def localCycle00157 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 6, .distance 5 6, .theta 5, .zero]
    constant := ![0, 2, 0, -1, -1, -1, -1, 3, 0, -1, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .triangle 8 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2, .triangle 10 0, .triangle 20 2, .triangle 24 2, .gapLower 6 1, .corridorLower 5 6, .thetaLower 5]

-- Original cycle e16c19ce0407eef8dc302e7086dd91ecce36d7fbdc16f680ef8c328674f9303b; original global index 17627.
def localCycle00158 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 4, .gapLower 6 4, .triangle 14 1]

-- Original cycle e3b1204540a70e975a07802236eeabb6003baaa7ae8155e2f24a441df53d4c24; original global index 17805.
def localCycle00159 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 32 0, .triangle 23 0, .gapLower 1 3, .triangle 20 0, .corridorLower 3 5]

-- Original cycle e5cd15d0d391f72eb1823b984c6b0497c0c3c9bab801546833d6c47b0d8d1bdb; original global index 17980.
def localCycle00160 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 17 2, .triangle 24 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle e5d611faf8eb97bcd0c7fdbb6ba5eb4b646eb4b792d941f37fc8b7c3754ce6a1; original global index 17983.
def localCycle00161 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 29 2, .gapLower 6 3, .triangle 11 1, .triangle 21 2, .gapLower 6 0]

-- Original cycle e5ec63fcddb9330acb40f46a0eedba7210eeafd5dceb5b97a6007ba18e7e5f56; original global index 17990.
def localCycle00162 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 8 1, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle e765dd85dc9d9cc488c05f1b3a87de762a30cd968e90a7b0001d079199420f4e; original global index 18100.
def localCycle00163 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 4 1, .gapLower 1 2, .gapLower 3 0]

-- Original cycle e7d13e01036f2d14ea575ae9c9b3e8422e11fa4dbb74b48108f1c2a9c608b922; original global index 18127.
def localCycle00164 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 28 0, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle e806949d5b1b67c128d4cd1339bb83aebcf1d3c00070b551a20ba090253e6759; original global index 18143.
def localCycle00165 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 28 2, .triangle 7 0, .triangle 8 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle e9553d27e748575cbd6470cd6aacf023a3137722954313c109258347f9f8400f; original global index 18236.
def localCycle00166 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 14 0, .triangle 12 1]

-- Original cycle eaf01f8d4cd272eab3f7f2966518c1546cd0f642b40b244e8f9d81cf7a1b5912; original global index 18350.
def localCycle00167 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -3, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 8 1, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle eb5b02fab2f76576a2b206e22486851e31274d7066536f46671a82364dfb41fb; original global index 18370.
def localCycle00168 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 31 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle ebb5e8e7c383c77a2b39a1b745f53f3dd950efcd0ba47f0945579c1808d2eb98; original global index 18394.
def localCycle00169 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .gapLower 6 4, .triangle 8 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle ee36250d63258f8004f1d080a2069cbb8c3fe4df22c4d3336304f7dfdcc147d6; original global index 18592.
def localCycle00170 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 32 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle ee884eaf566a62c977683ebb0a78f7a9db47d9a9e91605a81a1714414c535358; original global index 18614.
def localCycle00171 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 10 0, .triangle 33 2, .gapLower 6 2, .triangle 23 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Original cycle f05c96a0163ddfd62c555077a5357dd7dbf8a61b7e87f2cb24cea6edb77a5f30; original global index 18742.
def localCycle00172 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 10 0, .triangle 33 2, .gapLower 6 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle f2dc3ac732354715d0d9bf509d01745442886b0b5cb3ca7731ed22c886b2d633; original global index 18930.
def localCycle00173 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle f3f09af6c8528cb6808e7a82d6e13696f2e0b32bf91044a82577def89bb63753; original global index 19023.
def localCycle00174 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 5 1, .triangle 6 0, .triangle 25 1, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle f746593d77e9c11e615f224706068cdcc095a5ee61c769487170352260e047e9; original global index 19291.
def localCycle00175 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 31 0, .triangle 22 0, .triangle 23 0, .corridorLower 4 6, .thetaNext 3]

-- Original cycle f892ccc9916eb298c67b5069368e688e489ff82359fa8247e2a2e9efc1ea41af; original global index 19385.
def localCycle00176 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 2, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle f90c8e2597324cefa360270629c26eae5fc94b2e2907490d66ca53477fe3b054; original global index 19423.
def localCycle00177 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 6, .distance 3 6, .distance 0 3]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 11 2, .gapLower 6 2, .gapUpper 3 4]

-- Original cycle fa3efd54c1446268be71d6b7029b82339cce2ec842bd9d9b94ca7ea588fe6251; original global index 19516.
def localCycle00178 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle fad618e16131984facd520fd32e464142edddefeecb44f2c17ab970e321ccb0d; original global index 19572.
def localCycle00179 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 0 6, .distance 0 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 13 1]

-- Original cycle fbd3509eb653506cbad9c8e92afa6797390c9f708d9c5ddcc5198b0100e0008e; original global index 19660.
def localCycle00180 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 0 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 13 2, .gapLower 6 3, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle fbed79db820674782adec134fce1066e032ccb913cc9dd047d9fd5c85c145f71; original global index 19667.
def localCycle00181 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 5 1, .triangle 6 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle fc6868972c21f2ebebbfd80b3e1d1ffb37168ef26af757dcb557be87c56546d8; original global index 19717.
def localCycle00182 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .distance 1 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 26 1, .triangle 31 1, .triangle 19 0, .triangle 21 0, .corridorLower 3 6]

-- Original cycle fc6c5e3db6ecf956b1c6068f9943b479fda6aad892c3ccf715451c67fed24803; original global index 19719.
def localCycle00183 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle fd7273852156b70aef0fea6a2477f78c79fe11ae7c205fe730eccafb1375d779; original global index 19809.
def localCycle00184 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .gapLower 3 0]

-- Original cycle fec113bf82adb614ddc1e73c5cbadb8a4c82ac25180f8c851f416ab7f40d06d7; original global index 19920.
def localCycle00185 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 31 0, .triangle 34 0, .gapLower 5 1, .gapLower 1 3, .gapLower 4 0, .thetaNext 3]

-- Original cycle ff486d1bcd71555ffd18934528bc76d972bdb65e10425ca28fcb56c9c534ba02; original global index 19958.
def localCycle00186 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 18 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

def library : Library := fun id => if id < 93 then (if id < 46 then (if id < 23 then (if id < 11 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 8 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none))) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none))))) else (if id < 17 then (if id < 14 then (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none))) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)))) else (if id < 20 then (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none))) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)))))) else (if id < 34 then (if id < 28 then (if id < 25 then (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none)))) else (if id < 31 then (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none))) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none))))) else (if id < 40 then (if id < 37 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none)))) else (if id < 43 then (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none))) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))))))) else (if id < 69 then (if id < 57 then (if id < 51 then (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none)))) else (if id < 54 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none))) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none))))) else (if id < 63 then (if id < 60 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)))) else (if id < 66 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none))) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)))))) else (if id < 81 then (if id < 75 then (if id < 72 then (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none))) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)))) else (if id < 78 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none))))) else (if id < 87 then (if id < 84 then (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none))) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)))) else (if id < 90 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none))) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none)))))))) else (if id < 140 then (if id < 116 then (if id < 104 then (if id < 98 then (if id < 95 then (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)))) else (if id < 101 then (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none))))) else (if id < 110 then (if id < 107 then (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none))) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none)))) else (if id < 113 then (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none))) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none)))))) else (if id < 128 then (if id < 122 then (if id < 119 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none))) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)))) else (if id < 125 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none))) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none))))) else (if id < 134 then (if id < 131 then (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none))) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none)))) else (if id < 137 then (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none))) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none))))))) else (if id < 163 then (if id < 151 then (if id < 145 then (if id < 142 then (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none)) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none)))) else (if id < 148 then (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none))) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none))))) else (if id < 157 then (if id < 154 then (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none))) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none)))) else (if id < 160 then (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none))) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none)))))) else (if id < 175 then (if id < 169 then (if id < 166 then (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none))) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none)))) else (if id < 172 then (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id = 171 then some localCycle00171 else none))) else (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none))))) else (if id < 181 then (if id < 178 then (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none))) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none)))) else (if id < 184 then (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id = 183 then some localCycle00183 else none))) else (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![4, 2, 5, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 0, 5, 6, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 2, 0, 5, 6], ![1, 3, 0, 2, 4, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 34 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19456)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![4, 2, 5, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 0, 5, 6, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 2, 0, 6, 5], ![1, 3, 0, 2, 6, 4], ![1, 3, 0, 2, 5, 4]], proof := .tail 135 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19457)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![4, 2, 5, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 0, 6, 5, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 2, 0, 6, 5], ![1, 3, 0, 6, 2, 4], ![1, 3, 0, 5, 2, 4]], proof := .tail 65 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19458)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![4, 2, 6, 5, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 0, 6, 5, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 2, 0, 6, 5], ![1, 3, 6, 0, 2, 4], ![1, 3, 5, 0, 2, 4]], proof := .tail 82 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19459)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![4, 2, 6, 5, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 0, 6, 5, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 2, 0, 6, 5], ![1, 6, 3, 0, 2, 4], ![1, 5, 3, 0, 2, 4]], proof := .tail 14 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19460)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![4, 2, 6, 5, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 0, 6, 5, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 2, 0, 6, 5], ![6, 1, 3, 0, 2, 4], ![5, 1, 3, 0, 2, 4]], proof := .low6 (![48, 143, 171, 152, 50, 49, 70, 96, 172, 44, 87, 38, 106, 131, 42, 107, 38, 157, 21, 75, 38, 6, 25, 38, 180, 97, 169, 13]) }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19461)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![4, 6, 2, 5, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 0, 5, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 2, 0, 6, 5], ![1, 3, 6, 0, 2, 4], ![1, 3, 5, 2, 0, 4]], proof := .tail 36 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19462)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![4, 6, 2, 5, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 0, 5, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 2, 0, 6, 5], ![1, 6, 3, 0, 2, 4], ![1, 5, 3, 2, 0, 4]], proof := .tail 14 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19463)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![4, 6, 2, 5, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 6, 0, 5, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 2, 0, 6, 5], ![6, 1, 3, 0, 2, 4], ![5, 1, 3, 2, 0, 4]], proof := .low6 (![53, 31, 140, 178, 136, 179, 111, 28, 30, 45, 90, 45, 45, 124, 1, 165, 26, 26, 16, 60, 124, 124, 27, 118, 118, 102, 43, 162]) }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19464)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 0, 5, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 2, 6, 0, 5], ![1, 3, 6, 0, 2, 4], ![1, 3, 5, 2, 4, 0]], proof := .tail 32 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19465)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 0, 5, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 2, 6, 0, 5], ![1, 6, 3, 0, 2, 4], ![1, 5, 3, 2, 4, 0]], proof := .tail 14 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19466)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 6, 0, 5, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 2, 6, 0, 5], ![6, 1, 3, 0, 2, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 17 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19467)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 0, 5, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 6, 2, 0, 5], ![1, 3, 6, 0, 2, 4], ![1, 3, 5, 4, 2, 0]], proof := .tail 81 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19468)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 0, 5, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 6, 2, 0, 5], ![1, 6, 3, 0, 2, 4], ![1, 5, 3, 4, 2, 0]], proof := .tail 81 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19469)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 0, 5, 3], ![1, 6, 4, 5, 0, 2], ![1, 6, 3, 2, 0, 5], ![1, 6, 3, 0, 2, 4], ![1, 5, 4, 3, 2, 0]], proof := .tail 184 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19470)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 0, 5, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 6, 2, 0, 5], ![6, 1, 3, 0, 2, 4], ![5, 1, 3, 4, 2, 0]], proof := .tail 81 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19471)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 0, 5, 3], ![1, 6, 4, 5, 0, 2], ![1, 6, 3, 2, 0, 5], ![6, 1, 3, 0, 2, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 77 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19472)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 4, 0, 5, 3], ![1, 6, 4, 5, 0, 2], ![6, 1, 3, 2, 0, 5], ![6, 1, 3, 0, 2, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 149 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19473)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 4, 0, 5, 3], ![6, 1, 4, 5, 0, 2], ![6, 1, 3, 2, 0, 5], ![6, 1, 3, 0, 2, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 127 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19474)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 4, 0, 5, 3], ![6, 1, 4, 5, 0, 2], ![6, 1, 3, 2, 0, 5], ![6, 1, 3, 0, 2, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 67 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19475)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![4, 5, 2, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 0, 3, 6], ![1, 4, 5, 0, 2, 6], ![1, 3, 2, 0, 5, 6], ![1, 3, 2, 0, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 80 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19476)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![4, 5, 2, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 0, 6, 3], ![1, 4, 5, 0, 6, 2], ![1, 3, 2, 0, 5, 6], ![1, 3, 2, 0, 4, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 63 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19477)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![4, 5, 2, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 0, 6, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 2, 0, 5, 6], ![1, 3, 2, 0, 4, 6], ![1, 3, 0, 2, 4, 5]], proof := .low6 (![125, 61, 71, 84, 73, 33, 15, 76, 8, 161, 101, 23, 93, 177, 76, 76, 76, 76, 123, 176, 24, 120, 105, 58, 104, 40, 68, 3]) }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19478)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![4, 5, 2, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 0, 3, 6], ![1, 4, 5, 0, 2, 6], ![1, 3, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 99 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19479)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![4, 5, 2, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 0, 6, 3], ![1, 4, 5, 0, 6, 2], ![1, 3, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 4], ![1, 0, 3, 2, 5, 4]], proof := .tail 63 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19480)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![4, 5, 2, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 0, 6, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 4], ![1, 3, 0, 2, 5, 4]], proof := .tail 155 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19481)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![4, 5, 6, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 6, 0, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 2, 0, 5, 6], ![1, 3, 2, 0, 4, 6], ![1, 3, 2, 0, 4, 5]], proof := .low6 (![113, 117, 173, 139, 167, 33, 15, 22, 19, 37, 141, 57, 74, 126, 154, 79, 79, 79, 85, 19, 19, 19, 110, 108, 108, 59, 89, 3]) }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19482)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![4, 5, 6, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 6, 0, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 4], ![1, 3, 2, 0, 5, 4]], proof := .low6 (![113, 117, 173, 139, 158, 166, 111, 22, 19, 37, 54, 35, 186, 126, 154, 79, 35, 79, 85, 156, 19, 19, 137, 35, 108, 146, 92, 35]) }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19483)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![4, 6, 5, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 6, 0, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 2, 0, 6, 5], ![1, 3, 2, 6, 0, 4], ![1, 3, 2, 5, 0, 4]], proof := .tail 145 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19484)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![4, 6, 5, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 5, 0, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 2, 0, 6, 5], ![1, 3, 6, 2, 0, 4], ![1, 3, 5, 2, 0, 4]], proof := .tail 109 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19485)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![4, 6, 5, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 5, 0, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 2, 0, 6, 5], ![1, 6, 3, 2, 0, 4], ![1, 5, 3, 2, 0, 4]], proof := .tail 144 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19486)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![4, 6, 5, 2, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 6, 5, 0, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 2, 0, 6, 5], ![6, 1, 3, 2, 0, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 160 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19487)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 6, 0, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 2, 6, 0, 5], ![1, 3, 2, 6, 0, 4], ![1, 3, 2, 5, 4, 0]], proof := .tail 9 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19488)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 5, 0, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 2, 6, 0, 5], ![1, 3, 6, 2, 0, 4], ![1, 3, 5, 2, 4, 0]], proof := .tail 109 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19489)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 5, 0, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 2, 6, 0, 5], ![1, 6, 3, 2, 0, 4], ![1, 5, 3, 2, 4, 0]], proof := .tail 9 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19490)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 6, 5, 0, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 2, 6, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 9 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19491)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 5, 0, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 6, 2, 0, 5], ![1, 3, 6, 2, 0, 4], ![1, 3, 5, 4, 2, 0]], proof := .tail 138 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19492)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 5, 0, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 6, 2, 0, 5], ![1, 6, 3, 2, 0, 4], ![1, 5, 3, 4, 2, 0]], proof := .tail 138 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19493)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 5, 0, 3], ![1, 6, 4, 5, 0, 2], ![1, 6, 3, 2, 0, 5], ![1, 6, 3, 2, 0, 4], ![1, 5, 4, 3, 2, 0]], proof := .tail 64 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19494)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 5, 0, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 6, 2, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 1, 3, 4, 2, 0]], proof := .tail 138 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19495)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 5, 0, 3], ![1, 6, 4, 5, 0, 2], ![1, 6, 3, 2, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 69 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19496)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 4, 5, 0, 3], ![1, 6, 4, 5, 0, 2], ![6, 1, 3, 2, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 47 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19497)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 4, 5, 0, 3], ![6, 1, 4, 5, 0, 2], ![6, 1, 3, 2, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 182 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19498)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![6, 4, 5, 2, 3, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 4, 5, 0, 3], ![6, 1, 4, 5, 0, 2], ![6, 1, 3, 2, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 88 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19499)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![5, 4, 2, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 0, 3, 6], ![1, 4, 5, 0, 2, 6], ![1, 3, 2, 5, 0, 6], ![1, 3, 2, 4, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 39 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19500)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![5, 4, 2, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 0, 6, 3], ![1, 4, 5, 0, 6, 2], ![1, 3, 2, 5, 0, 6], ![1, 3, 2, 4, 0, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 181 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19501)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![5, 4, 2, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 0, 6, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 2, 5, 0, 6], ![1, 3, 2, 4, 0, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 148 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19502)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![5, 4, 6, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 6, 0, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 2, 5, 0, 6], ![1, 3, 2, 4, 0, 6], ![1, 3, 2, 0, 4, 5]], proof := .tail 56 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19503)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 6, 0, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 2, 5, 6, 0], ![1, 3, 2, 4, 0, 6], ![1, 3, 2, 4, 0, 5]], proof := .tail 129 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19504)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 6, 0, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 2, 5, 6, 0], ![1, 3, 2, 4, 6, 0], ![1, 3, 2, 4, 5, 0]], proof := .tail 115 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19505)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 6, 0, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 2, 6, 5, 0], ![1, 3, 2, 6, 4, 0], ![1, 3, 2, 5, 4, 0]], proof := .tail 78 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19506)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 5, 0, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 2, 6, 5, 0], ![1, 3, 6, 2, 4, 0], ![1, 3, 5, 2, 4, 0]], proof := .tail 147 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19507)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 5, 0, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 2, 6, 5, 0], ![1, 6, 3, 2, 4, 0], ![1, 5, 3, 2, 4, 0]], proof := .tail 134 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19508)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 5, 0, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 6, 2, 5, 0], ![1, 3, 6, 2, 4, 0], ![1, 3, 5, 4, 2, 0]], proof := .tail 116 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19509)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 5, 0, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 6, 2, 5, 0], ![1, 6, 3, 2, 4, 0], ![1, 5, 3, 4, 2, 0]], proof := .tail 83 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19510)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 5, 0, 3], ![1, 6, 4, 5, 0, 2], ![1, 6, 3, 2, 5, 0], ![1, 6, 3, 2, 4, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 150 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19511)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 6, 5, 0, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 2, 6, 5, 0], ![6, 1, 3, 2, 4, 0], ![5, 1, 3, 2, 4, 0]], proof := .tail 134 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19512)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 5, 0, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 6, 2, 5, 0], ![6, 1, 3, 2, 4, 0], ![5, 1, 3, 4, 2, 0]], proof := .tail 83 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19513)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 5, 0, 3], ![1, 6, 4, 5, 0, 2], ![1, 6, 3, 2, 5, 0], ![6, 1, 3, 2, 4, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 150 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19514)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 4, 5, 0, 3], ![1, 6, 4, 5, 0, 2], ![6, 1, 3, 2, 5, 0], ![6, 1, 3, 2, 4, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 114 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19515)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 4, 5, 0, 3], ![6, 1, 4, 5, 0, 2], ![6, 1, 3, 2, 5, 0], ![6, 1, 3, 2, 4, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 10 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19516)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 4, 5, 0, 3], ![6, 1, 4, 5, 0, 2], ![6, 1, 3, 2, 5, 0], ![6, 1, 3, 2, 4, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 20 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19517)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![5, 4, 2, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 4, 0, 3, 6], ![1, 4, 5, 0, 2, 6], ![1, 3, 5, 2, 0, 6], ![1, 3, 4, 2, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 164 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19518)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![5, 4, 2, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 4, 0, 6, 3], ![1, 4, 5, 0, 6, 2], ![1, 3, 5, 2, 0, 6], ![1, 3, 4, 2, 0, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 62 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19519)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![5, 4, 2, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 4, 0, 6, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 5, 2, 0, 6], ![1, 3, 4, 2, 0, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 62 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19520)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![5, 4, 6, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 4, 6, 0, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 5, 2, 0, 6], ![1, 3, 4, 2, 0, 6], ![1, 3, 2, 0, 4, 5]], proof := .tail 95 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19521)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 4, 6, 0, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 5, 2, 6, 0], ![1, 3, 4, 2, 0, 6], ![1, 3, 2, 4, 0, 5]], proof := .tail 5 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19522)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 4, 0, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 5, 6, 2, 0], ![1, 3, 4, 2, 0, 6], ![1, 3, 4, 2, 0, 5]], proof := .tail 133 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19523)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 4, 6, 0, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 5, 2, 6, 0], ![1, 3, 4, 2, 6, 0], ![1, 3, 2, 4, 5, 0]], proof := .tail 91 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19524)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 4, 0, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 5, 6, 2, 0], ![1, 3, 4, 2, 6, 0], ![1, 3, 4, 2, 5, 0]], proof := .tail 115 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19525)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 4, 0, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 5, 6, 2, 0], ![1, 3, 4, 6, 2, 0], ![1, 3, 4, 5, 2, 0]], proof := .tail 46 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19526)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 4, 0, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 6, 5, 2, 0], ![1, 3, 6, 4, 2, 0], ![1, 3, 5, 4, 2, 0]], proof := .tail 11 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19527)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 4, 0, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 6, 5, 2, 0], ![1, 6, 3, 4, 2, 0], ![1, 5, 3, 4, 2, 0]], proof := .tail 62 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19528)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 4, 0, 3], ![1, 6, 4, 5, 0, 2], ![1, 6, 3, 5, 2, 0], ![1, 6, 3, 4, 2, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 66 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19529)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 5, 4, 0, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 6, 5, 2, 0], ![6, 1, 3, 4, 2, 0], ![5, 1, 3, 4, 2, 0]], proof := .tail 62 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19530)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 5, 4, 0, 3], ![1, 6, 4, 5, 0, 2], ![1, 6, 3, 5, 2, 0], ![6, 1, 3, 4, 2, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 66 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19531)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 5, 4, 0, 3], ![1, 6, 4, 5, 0, 2], ![6, 1, 3, 5, 2, 0], ![6, 1, 3, 4, 2, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 51 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19532)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 5, 4, 0, 3], ![6, 1, 4, 5, 0, 2], ![6, 1, 3, 5, 2, 0], ![6, 1, 3, 4, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 132 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19533)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 5, 4, 0, 3], ![6, 1, 4, 5, 0, 2], ![6, 1, 3, 5, 2, 0], ![6, 1, 3, 4, 2, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 132 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19534)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![5, 4, 2, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 4, 0, 3, 6], ![1, 5, 4, 0, 2, 6], ![1, 5, 3, 2, 0, 6], ![1, 4, 3, 2, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 121 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19535)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![5, 4, 2, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 4, 0, 6, 3], ![1, 5, 4, 0, 6, 2], ![1, 5, 3, 2, 0, 6], ![1, 4, 3, 2, 0, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 174 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19536)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![5, 4, 2, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 4, 0, 6, 3], ![1, 5, 4, 6, 0, 2], ![1, 5, 3, 2, 0, 6], ![1, 4, 3, 2, 0, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 100 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19537)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![5, 4, 6, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 4, 6, 0, 3], ![1, 5, 4, 6, 0, 2], ![1, 5, 3, 2, 0, 6], ![1, 4, 3, 2, 0, 6], ![1, 3, 2, 0, 4, 5]], proof := .tail 12 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19538)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 4, 6, 0, 3], ![1, 5, 4, 6, 0, 2], ![1, 5, 3, 2, 6, 0], ![1, 4, 3, 2, 0, 6], ![1, 3, 2, 4, 0, 5]], proof := .tail 98 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19539)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 4, 0, 3], ![1, 5, 4, 6, 0, 2], ![1, 5, 3, 6, 2, 0], ![1, 4, 3, 2, 0, 6], ![1, 3, 4, 2, 0, 5]], proof := .tail 81 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19540)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 4, 0, 3], ![1, 5, 6, 4, 0, 2], ![1, 5, 6, 3, 2, 0], ![1, 4, 3, 2, 0, 6], ![1, 4, 3, 2, 0, 5]], proof := .tail 94 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19541)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 4, 6, 0, 3], ![1, 5, 4, 6, 0, 2], ![1, 5, 3, 2, 6, 0], ![1, 4, 3, 2, 6, 0], ![1, 3, 2, 4, 5, 0]], proof := .tail 52 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19542)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 4, 0, 3], ![1, 5, 4, 6, 0, 2], ![1, 5, 3, 6, 2, 0], ![1, 4, 3, 2, 6, 0], ![1, 3, 4, 2, 5, 0]], proof := .tail 81 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19543)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 4, 0, 3], ![1, 5, 6, 4, 0, 2], ![1, 5, 6, 3, 2, 0], ![1, 4, 3, 2, 6, 0], ![1, 4, 3, 2, 5, 0]], proof := .tail 7 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19544)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 4, 0, 3], ![1, 5, 4, 6, 0, 2], ![1, 5, 3, 6, 2, 0], ![1, 4, 3, 6, 2, 0], ![1, 3, 4, 5, 2, 0]], proof := .tail 103 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19545)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 4, 0, 3], ![1, 5, 6, 4, 0, 2], ![1, 5, 6, 3, 2, 0], ![1, 4, 3, 6, 2, 0], ![1, 4, 3, 5, 2, 0]], proof := .tail 103 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19546)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 4, 0, 3], ![1, 6, 5, 4, 0, 2], ![1, 5, 6, 3, 2, 0], ![1, 4, 6, 3, 2, 0], ![1, 4, 5, 3, 2, 0]], proof := .tail 163 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19547)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 4, 0, 3], ![1, 6, 5, 4, 0, 2], ![1, 6, 5, 3, 2, 0], ![1, 6, 4, 3, 2, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 185 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19548)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 5, 4, 0, 3], ![1, 6, 5, 4, 0, 2], ![1, 6, 5, 3, 2, 0], ![6, 1, 4, 3, 2, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 168 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19549)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 5, 4, 0, 3], ![1, 6, 5, 4, 0, 2], ![6, 1, 5, 3, 2, 0], ![6, 1, 4, 3, 2, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 175 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19550)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 5, 4, 0, 3], ![6, 1, 5, 4, 0, 2], ![6, 1, 5, 3, 2, 0], ![6, 1, 4, 3, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 175 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19551)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 5, 4, 0, 3], ![6, 1, 5, 4, 0, 2], ![6, 1, 5, 3, 2, 0], ![6, 1, 4, 3, 2, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 67 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19552)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![5, 4, 2, 3, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 4, 0, 3, 6], ![1, 5, 4, 0, 2, 6], ![5, 1, 3, 2, 0, 6], ![4, 1, 3, 2, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 41 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19553)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![5, 4, 2, 3, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 4, 0, 6, 3], ![1, 5, 4, 0, 6, 2], ![5, 1, 3, 2, 0, 6], ![4, 1, 3, 2, 0, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 4 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19554)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![5, 4, 2, 6, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 4, 0, 6, 3], ![1, 5, 4, 6, 0, 2], ![5, 1, 3, 2, 0, 6], ![4, 1, 3, 2, 0, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 4 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19555)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![5, 4, 6, 2, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 4, 6, 0, 3], ![1, 5, 4, 6, 0, 2], ![5, 1, 3, 2, 0, 6], ![4, 1, 3, 2, 0, 6], ![1, 3, 2, 0, 4, 5]], proof := .tail 29 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19556)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 4, 6, 0, 3], ![1, 5, 4, 6, 0, 2], ![5, 1, 3, 2, 6, 0], ![4, 1, 3, 2, 0, 6], ![1, 3, 2, 4, 0, 5]], proof := .tail 119 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19557)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 6, 4, 0, 3], ![1, 5, 4, 6, 0, 2], ![5, 1, 3, 6, 2, 0], ![4, 1, 3, 2, 0, 6], ![1, 3, 4, 2, 0, 5]], proof := .tail 81 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19558)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 6, 4, 0, 3], ![1, 5, 6, 4, 0, 2], ![5, 1, 6, 3, 2, 0], ![4, 1, 3, 2, 0, 6], ![1, 4, 3, 2, 0, 5]], proof := .tail 170 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19559)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![2, 3, 5, 6, 4, 0], ![1, 5, 6, 4, 0, 3], ![1, 5, 6, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 1, 3, 2, 0, 6], ![4, 1, 3, 2, 0, 5]], proof := .tail 122 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19560)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 4, 6, 0, 3], ![1, 5, 4, 6, 0, 2], ![5, 1, 3, 2, 6, 0], ![4, 1, 3, 2, 6, 0], ![1, 3, 2, 4, 5, 0]], proof := .tail 7 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19561)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 6, 4, 0, 3], ![1, 5, 4, 6, 0, 2], ![5, 1, 3, 6, 2, 0], ![4, 1, 3, 2, 6, 0], ![1, 3, 4, 2, 5, 0]], proof := .tail 81 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19562)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 6, 4, 0, 3], ![1, 5, 6, 4, 0, 2], ![5, 1, 6, 3, 2, 0], ![4, 1, 3, 2, 6, 0], ![1, 4, 3, 2, 5, 0]], proof := .tail 170 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19563)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 5, 4, 0, 3], ![1, 5, 4, 6, 0, 2], ![5, 1, 3, 6, 2, 0], ![4, 1, 3, 6, 2, 0], ![1, 3, 4, 5, 2, 0]], proof := .tail 103 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19564)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 5, 4, 0, 3], ![1, 5, 6, 4, 0, 2], ![5, 1, 6, 3, 2, 0], ![4, 1, 3, 6, 2, 0], ![1, 4, 3, 5, 2, 0]], proof := .tail 103 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19565)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 5, 4, 0, 3], ![1, 6, 5, 4, 0, 2], ![5, 1, 6, 3, 2, 0], ![4, 1, 6, 3, 2, 0], ![1, 4, 5, 3, 2, 0]], proof := .tail 0 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19566)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 5, 6, 4, 0], ![1, 5, 6, 4, 0, 3], ![1, 5, 6, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 1, 3, 2, 6, 0], ![4, 1, 3, 2, 5, 0]], proof := .tail 7 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19567)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 5, 6, 4, 0], ![1, 6, 5, 4, 0, 3], ![1, 5, 6, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 1, 3, 6, 2, 0], ![4, 1, 3, 5, 2, 0]], proof := .tail 103 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19568)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 5, 6, 4, 0], ![1, 6, 5, 4, 0, 3], ![1, 6, 5, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 1, 6, 3, 2, 0], ![4, 1, 5, 3, 2, 0]], proof := .tail 0 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19569)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 6, 5, 4, 0], ![1, 6, 5, 4, 0, 3], ![1, 6, 5, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 6, 1, 3, 2, 0], ![4, 5, 1, 3, 2, 0]], proof := .tail 18 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19570)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 3, 6, 5, 4, 0], ![1, 6, 5, 4, 0, 3], ![1, 6, 5, 4, 0, 2], ![6, 5, 1, 3, 2, 0], ![6, 4, 1, 3, 2, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 86 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19571)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 6, 3, 5, 4, 0], ![1, 6, 5, 4, 0, 3], ![6, 1, 5, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 6, 1, 3, 2, 0], ![4, 5, 3, 1, 2, 0]], proof := .tail 183 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19572)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 6, 3, 5, 4, 0], ![1, 6, 5, 4, 0, 3], ![6, 1, 5, 4, 0, 2], ![6, 5, 1, 3, 2, 0], ![6, 4, 1, 3, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 55 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19573)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 2, 3, 5, 4, 0], ![6, 1, 5, 4, 0, 3], ![6, 1, 5, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 6, 1, 3, 2, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 153 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19574)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 2, 3, 5, 4, 0], ![6, 1, 5, 4, 0, 3], ![6, 1, 5, 4, 0, 2], ![6, 5, 1, 3, 2, 0], ![6, 4, 1, 3, 2, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 67 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19575)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![5, 4, 2, 3, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 4, 0, 3, 6], ![5, 1, 4, 0, 2, 6], ![5, 1, 3, 2, 0, 6], ![4, 3, 1, 2, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 72 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19576)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![5, 4, 2, 3, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 4, 0, 6, 3], ![5, 1, 4, 0, 6, 2], ![5, 1, 3, 2, 0, 6], ![4, 3, 1, 2, 0, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 112 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19577)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![5, 4, 2, 6, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 4, 0, 6, 3], ![5, 1, 4, 6, 0, 2], ![5, 1, 3, 2, 0, 6], ![4, 3, 1, 2, 0, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 2 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19578)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![5, 4, 6, 2, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 4, 6, 0, 3], ![5, 1, 4, 6, 0, 2], ![5, 1, 3, 2, 0, 6], ![4, 3, 1, 2, 0, 6], ![1, 3, 2, 0, 4, 5]], proof := .tail 130 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19579)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 4, 6, 0, 3], ![5, 1, 4, 6, 0, 2], ![5, 1, 3, 2, 6, 0], ![4, 3, 1, 2, 0, 6], ![1, 3, 2, 4, 0, 5]], proof := .tail 151 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19580)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 6, 4, 0, 3], ![5, 1, 4, 6, 0, 2], ![5, 1, 3, 6, 2, 0], ![4, 3, 1, 2, 0, 6], ![1, 3, 4, 2, 0, 5]], proof := .tail 142 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19581)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 6, 4, 0, 3], ![5, 1, 6, 4, 0, 2], ![5, 1, 6, 3, 2, 0], ![4, 3, 1, 2, 0, 6], ![1, 4, 3, 2, 0, 5]], proof := .tail 159 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19582)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![2, 5, 3, 6, 4, 0], ![1, 5, 6, 4, 0, 3], ![5, 1, 6, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 3, 1, 2, 0, 6], ![4, 1, 3, 2, 0, 5]], proof := .tail 128 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19583)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (19456 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 19456 ≤ id.val) (hhigh : id.val < 19584) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 19456)) = true := by
  let j : Fin 128 := ⟨id.val - 19456, by omega⟩
  have hsum : 19456 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (19456 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard152
