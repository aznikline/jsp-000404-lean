import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard049
open N4R2RowDataReplay

-- Original cycle 009fbb33b0d2e1eed80b529137027984dbfd4dc15f508aab5087774b927b9330; original global index 58.
def localCycle00000 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 9 2, .triangle 13 0, .triangle 34 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 0235e5ec35c96b652c7fbc8351e3a9b37d64ac60b6362ae746cb4232d9ace894; original global index 174.
def localCycle00001 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 29 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 0236c8d968a3245b941d267f49df6c493d3b1192e040a9479b3a693f969a2559; original global index 175.
def localCycle00002 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 0 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -2, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, true, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 14 2, .gapLower 6 1, .triangle 30 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 02abec45e8353837749761c6603736dd9aa1295fa559c5bb833192381516fa8f; original global index 209.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 13 2, .gapLower 6 2, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .thetaNext 1, .thetaLower 1]

-- Original cycle 03458773f770bd7ddcba6676d6e503e39fe4dd140b3aa9236e4176e7cf68f6b9; original global index 262.
def localCycle00004 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 8 1, .gapUpper 2 4]

-- Original cycle 0350675d9fe701e4107edda755e4bfb686569af5b2db300622902a759a00eb9c; original global index 268.
def localCycle00005 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, 0, -1, -1, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .gapLower 6 3, .triangle 14 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle 0362224bc6cb608442cf4794a2cd945fd69d310f15ac3640ea270c1540104f15; original global index 273.
def localCycle00006 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 3 6, .distance 0 3, .distance 0 1]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 1 1, .triangle 21 1, .triangle 11 0, .gapLower 0 1]

-- Original cycle 04911b1cabb647805ad1b8d0a8ff4ca8d9dc1df024e9dac77d31de7b49f48c25; original global index 359.
def localCycle00007 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 3, .distance 0 1]
    constant := ![2, 0, 0, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, true, false] }
  origin := ![.gapUpper 1 1, .triangle 4 2, .triangle 11 1, .gapLower 0 1]

-- Original cycle 0569fa5172343856cf3234e7d44092c5ca57fc753d793f0c20b427427c79da50; original global index 440.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 4, .distance 0 6, .distance 0 3, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 31 1, .gapLower 4 3, .gapLower 0 3, .gapLower 0 2, .gapLower 3 1, .corridorLower 2 3]

-- Original cycle 0582329802e2f2ca77bbcb4e10c5fe4d0eb6070e833f940587e5f51bf89aa24d; original global index 448.
def localCycle00009 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 33 2, .triangle 11 2, .gapLower 6 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 05f25becb20822bc4aadd8b17606b2774e8836ebed5036cbf4e39e9a0da31652; original global index 494.
def localCycle00010 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 8 2, .gapLower 6 1, .gapUpper 2 4]

-- Original cycle 06cf9950f712a612160bdf709685ec32e6629f724cfab4b64efd3d21ed8468c3; original global index 561.
def localCycle00011 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 6, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, 0, -2, -2, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.triangle 7 2, .triangle 14 2, .gapLower 6 2, .gapLower 6 1, .gapUpper 2 4]

-- Original cycle 08526670fb79ea7e5788827bbd5d2cf6520794c9109b58b08296a3035d35a908; original global index 662.
def localCycle00012 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 6, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -2, 2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 2, .triangle 29 0, .gapLower 6 0, .gapLower 6 6, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 09778e4fca5d5fd500bf01d80eae28eb5dc4baf34c62a3384c7faa07b94859a6; original global index 752.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 099dc3a8a1d37205b1d945c14a868fda25b9ab1233d681b0fad563c465b8fee4; original global index 767.
def localCycle00014 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 0, .triangle 19 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 0a6b47893c82e7374a608ee743f76cd7e8eb6d203d36f28ecba78a1502470627; original global index 829.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 0b46b064904f51d600f32b50191f63c7a59f110848aed5f51c2950da93e7eb65; original global index 906.
def localCycle00016 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 21 2, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 0c0b5f00c94a741246399922590b1759ba0dcca8b7992d7dae82eb1b7bc55dcf; original global index 951.
def localCycle00017 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .gapLower 5 3, .gapLower 0 4, .gapLower 4 2, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 0c6f60d9f5dec444cd4e204ba25f4695c03f266c7ed0a243aa6e57af8c3fe150; original global index 984.
def localCycle00018 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 3, .gapUpper 5 3]

-- Original cycle 0ccc57a49816b15c21aa2c118b09b6022b9daabcef33ef99dc4468ea8c0b7bbf; original global index 1012.
def localCycle00019 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .triangle 4 2, .gapLower 6 3, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 0d8b221b5708f5b35ad975ef4f0c6426828e59276258982e0c5e12ecf6959822; original global index 1071.
def localCycle00020 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 0e307303a4a75df1c4f6b22eb7279a2f58e6a0982e9093b3a8ea29a0ec8743d6; original global index 1117.
def localCycle00021 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 3]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 3 2, .triangle 11 2, .gapLower 0 2]

-- Original cycle 0e6bcb9b0816561c4a3eb4b8811beade6897f4c905917d424e6d8cb9e15f6f9c; original global index 1142.
def localCycle00022 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 34 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 0f22c7b6d46647e332e1cd43b6b398207d66a719b9d6c00a156d52108b9ee867; original global index 1204.
def localCycle00023 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 0, .triangle 12 0, .triangle 13 0, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 1148d3af39ede44f30ff7c5fe2730801999046300566ae73a9a20cf086810c39; original global index 1375.
def localCycle00024 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .gapLower 6 4, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 11cf564e2b09994283d2b78e2e581d56e70530cb38de96c5af86b05ba4cac3f9; original global index 1419.
def localCycle00025 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 10 2, .triangle 14 0, .triangle 30 0, .gapLower 2 2, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 126fba92ecad77a7888359d95319d8dfdb7806cb4b4413a41a55cfb47595bc98; original global index 1464.
def localCycle00026 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 2 6, .distance 2 3, .theta 3]
    constant := ![3, -1, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 32 2, .gapLower 6 3, .triangle 8 1, .triangle 27 1, .gapLower 3 0]

-- Original cycle 131f2985c89d090fbce3a276628dd346b328933668978127cba1c2ebb0f3d33b; original global index 1512.
def localCycle00027 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 135ed1a2606f5edd7a3bd1697c9e345ca0ce6a263d7cea42dfd0037b0d1bfa34; original global index 1525.
def localCycle00028 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .triangle 13 2, .triangle 14 1, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4]

-- Original cycle 138c49a31da32a71ec0a4c6efe024a53ecb852bcfcfa732fc993c95fc48495b5; original global index 1541.
def localCycle00029 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 0, .triangle 28 2, .triangle 30 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 1494c009206adfbb760d5cc9d91aa3d332ffbf82b844fc23c94cd19ca0e72fe9; original global index 1633.
def localCycle00030 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .gapLower 2 2, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 14b6488675b578066b1be2d84581245a08b4ea174a506f9351d8731d8dd5edb6; original global index 1642.
def localCycle00031 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 2, 0, -1, -1, -1, -1, 3, 0, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 17 2, .triangle 24 0, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 14bc497eff1729289a3cabdcccbcb3a4398097195d812f69b6439ee5770ed1d6; original global index 1643.
def localCycle00032 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 13 2, .gapLower 6 1, .corridorLower 2 6, .thetaLower 2]

-- Original cycle 1662fcf5fb26fbc06c791de65551ead90e44cd573b362cc2824ae4c017af70a5; original global index 1760.
def localCycle00033 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 32 0, .triangle 13 2, .triangle 14 1, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4]

-- Original cycle 16bdb1a4785f9ec97a734e5b70aa060f8ae025968cf4e3cbb0a5e0073e4a1f3e; original global index 1786.
def localCycle00034 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 17ceb5e8f9c3505345745e2ac4b2ccb7042b1d8767d70f2d3ab24415f0714fc7; original global index 1860.
def localCycle00035 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 5 6]

-- Original cycle 1838cc6bfad2c0b2eb83fd6f3a00ac0c0fba973f8d6c7be7f534e2aa1e8946aa; original global index 1893.
def localCycle00036 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![2, 0, -1, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 5 4, .triangle 10 0, .gapLower 0 1]

-- Original cycle 187181451c54cfaa43b8cabf624a66100daee2c8377399489174cc5cec920d0c; original global index 1913.
def localCycle00037 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 19eec0f93068105598fcdbfae034b55c395a0ebb24555a2079f7015c4e5d3ffc; original global index 2025.
def localCycle00038 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![4, 0, -1, -1, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 4 6, .gapLower 5 5, .triangle 20 0, .triangle 21 0, .gapLower 6 3, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle 1a17c8dab011af5f58b9ac8956449dac77988dfb282991a306522423c4832d52; original global index 2037.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 3 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 27 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 1a258f0675119dcf38228295eecd8e034c978b32d76f60a2c85f40a1c3996a4e; original global index 2042.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 9 2, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 1ce21dc2da897fd00826e4c0684a5423650ad275dd6c0652439977c1c879de66; original global index 2223.
def localCycle00041 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 1d034ed464dc7b2564f0ac85ec86484f79fce4f33281f1ce5d1983ccd18a86a2; original global index 2236.
def localCycle00042 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 33 2, .gapLower 6 3, .triangle 8 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 22fd1916b92c90b57e3885e326af79405b3049d40741dd61922ec8fec5716f88; original global index 2684.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 24 2, .gapLower 6 3, .triangle 14 1, .triangle 30 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 235794de2602f83490bf5c7fc27e8d3e9e63a86a68598047642a9a4ee7346bc7; original global index 2708.
def localCycle00044 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![2, 0, -1, -3, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true, true] }
  origin := ![.gapUpper 2 5, .triangle 15 2, .triangle 21 0, .gapLower 6 2, .triangle 8 1, .gapUpper 2 4]

-- Original cycle 2369d91697bc5b471c3828a3b50b209ca8bcbecbe4e42761927318152f7f332d; original global index 2718.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 21 1, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 23a889582aa133e5427c577004c28844293bd1f1c862608dfb1e5eaf626276b5; original global index 2735.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 24279910ab9f91550e69c2f0b4bee30197281ccefb7b6fce29bf6317929c5e66; original global index 2773.
def localCycle00047 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 243a1d432f1c3f88b4aa0f25086fbef5ebedcef62e48fdd36f5adfeeef794d16; original global index 2778.
def localCycle00048 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 31 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 24554017f800536fc47788bba02c9aa14ff7fe97ca556b7951f23b2c87486412; original global index 2785.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .gapLower 0 3, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 24e1e8086ea466959d2945aa01bd6c1e31b9a4a5cce711b009184058ade0462d; original global index 2828.
def localCycle00050 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 5, .distance 0 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 2, .gapLower 0 4, .gapLower 0 3, .gapLower 4 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 25064a411191cad7fedcd7df972db2417dd73830fa818964a86209aa5bcb4e19; original global index 2844.
def localCycle00051 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .triangle 8 1, .triangle 27 1, .corridorLower 2 3]

-- Original cycle 25512b7d655d3d078c405dba0c63b578338f8e2e4c732f895a798440bf680d13; original global index 2868.
def localCycle00052 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 8 1, .gapUpper 2 4]

-- Original cycle 25527696da1070b279f29b6e6c7ccaaa4103dcef6d57f66434ea874471c8d1f9; original global index 2870.
def localCycle00053 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 32 2, .gapLower 6 3, .triangle 8 1, .triangle 29 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 262e8760a3595cb0a10d62795b2a47650dccaec77d64dc9a76f5b004f09d5152; original global index 2927.
def localCycle00054 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 26322c951c452d9770f18920619313c7681937ea01e43bc3f13a952f80fcddcb; original global index 2928.
def localCycle00055 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -2, 3, 0, -2, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 27280268b9c0265b79baea55395cfa10dde5d27622457c45c5b12c68b7eda516; original global index 2998.
def localCycle00056 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 3 6, .distance 5 6, .distance 0 6, .distance 2 6, .distance 2 5, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 33 1, .gapLower 6 2, .triangle 8 1, .triangle 30 1, .gapLower 5 0]

-- Original cycle 272d8d04f3fd67696fcb58dce761c2834933400b365d4aa078391f22e377d5d2; original global index 2999.
def localCycle00057 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 27362dbd7fbc4c3edd56936d97e6ce4a7102d719e6919773fe01938e7558eca7; original global index 3000.
def localCycle00058 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .triangle 14 1, .triangle 30 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 2737e04a45238e5cf9e0c5704120bd95f9599e54612c2aa2a3a36d7d91099cf7; original global index 3001.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 9 2, .triangle 12 0, .triangle 34 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4]

-- Original cycle 27f50e32d657fb97685a8ca2b06998ed96e334e210dc4db1086a9813b67152cd; original global index 3060.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 32 2, .triangle 11 2, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 282cdbc4106c39fef3e121fe4ef59b2f3f58c51827330e4c3681d206d92237a3; original global index 3072.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 5 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 24 0, .gapLower 6 2, .triangle 8 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 2897728f0f36b36269e4d87745f5d785dcda42e3b7535b104fa02a6592ce81bc; original global index 3106.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 28b83efdd499e70f82ac8e9d3d83df4ba4cb0d05f3792540bf279b7039e98d57; original global index 3116.
def localCycle00063 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 3, .gapUpper 4 5, .gapLower 6 4, .triangle 21 0]

-- Original cycle 2942b644f38669a2a8ce78361c192a6f72122376f9b9d62b2975235d0f0889f7; original global index 3150.
def localCycle00064 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 4 2, .gapLower 6 3, .corridorLower 2 6, .thetaLower 2]

-- Original cycle 29dba322d1dc695d0407ae293cfff6f49c3b1e530009c3b095f559ad7ea2632a; original global index 3194.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![4, 0, -1, -1, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 31 2, .triangle 20 0, .triangle 21 0, .gapLower 6 3, .gapLower 6 2, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle 29ef4ce34cd4a385493b21317c548c9c90645f966eb9f78d59c3ffbf6919d934; original global index 3200.
def localCycle00066 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 4 2, .triangle 8 1, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 2aed907119afbd2bb467805321909137cfc6fd50cbf7a7cd842d4ad997cd54a2; original global index 3273.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 6, .distance 2 6, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 2, .triangle 8 1, .gapLower 6 2, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 2b1356dd7bfdd3104d8a38096dad747a7e0bf80e548dec1e0cda5da320cf9d1f; original global index 3291.
def localCycle00068 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 21 1, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 2c2f0c9364d929c2fc97283f86c1ea2f39b931afd45fa330cc334ff17bfc6453; original global index 3383.
def localCycle00069 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 2db252f13286196fe50cbee17d54ccd485042b5f7756b0be11c8498bbf7685d8; original global index 3489.
def localCycle00070 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 4 2, .triangle 8 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 2dce5619a65aa98f0dd0ddd18ed1d461548124c0ea04aa2050afc183102b6a28; original global index 3496.
def localCycle00071 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 9 2, .triangle 13 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 2f37c90ca937028728ef3484ee935e045728a1fce89a42b7317bf77d65f04080; original global index 3606.
def localCycle00072 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 6, .distance 2 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 8 1, .triangle 29 1, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 31843955bffb1e740b425462bb9b49d4e913a31de49e12a394e883c0244fd09e; original global index 3775.
def localCycle00073 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 2, .distance 2 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, -1, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 8 0, .triangle 29 1, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 3251002ed217b3fad20ef0660ef5dae93ffe4a586cc3bae4ead71b3fa0f10c6d; original global index 3844.
def localCycle00074 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 2, .gapLower 6 4, .triangle 27 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 32cb4ac079afb600d876b869d97bb28e34d55f1811c913691e63e07e611b15ad; original global index 3890.
def localCycle00075 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 2 6, .distance 2 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 2, 0, -1, -1, -1, -1, 3, 0, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 21 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2, .triangle 8 2, .gapLower 6 1, .triangle 29 1, .triangle 28 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle 33ee141202852320fa559234ce96ee93c9124271f07fed58497beafb48c38d8e; original global index 3977.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 0 6, .distance 2 6, .distance 2 5, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .gapLower 6 2, .gapLower 6 1, .triangle 30 1, .gapLower 5 0]

-- Original cycle 344bb4ad91cfa0bb87f5ebc96c47c99be89e6e94a45e3236629183a34ac192a6; original global index 4009.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 20 2, .triangle 24 2, .gapLower 6 4, .triangle 27 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 34809bbb3a71e655ae17b243751a1caa03906165cfe0ddf0f06e9fe16e880848; original global index 4019.
def localCycle00078 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 368964289fdb53a2c6972b35dd23d22c516ee03600922d93c8413b5b380b7cd8; original global index 4186.
def localCycle00079 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 2, .gapLower 6 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 393655b19280e35bb2f95eea8dd8ccfad106af15456e9d90907c7b97eeed583c; original global index 4402.
def localCycle00080 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 0, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 393f5dce4c35096d60baa06bd8dfa71374b39ca36f6518231c17a82160d4651c; original global index 4404.
def localCycle00081 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 4 6, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 34 1]

-- Original cycle 39843be152de7dc414458c80668c38744dbd40e1e8f294810cd8f3a9bfd98df5; original global index 4431.
def localCycle00082 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 6 4, .triangle 8 1, .triangle 27 1, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 3a5d1075f423b0cdd37bbc8180c52206ccbe7e1d72d4347eae5d3b93b52f4837; original global index 4507.
def localCycle00083 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 4 3, .triangle 9 0, .gapLower 0 1]

-- Original cycle 3ace139b9d4a96405d65168cd4f7d9b82cd23cc387c4fef31f5a7316e66df82b; original global index 4544.
def localCycle00084 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 5, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -2, -1, 3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 0, .triangle 30 2, .gapLower 6 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 3bc6b3d9df9ce37b3f2673f12aa2298d0ada3ea7d724ebaa7c0f2f9ba72a7bcc; original global index 4623.
def localCycle00085 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 33 1, .gapLower 5 2, .gapLower 0 3, .gapLower 0 2, .gapLower 3 1, .corridorLower 2 3]

-- Original cycle 3bdaf10418069d3f34127a5c99b449356aa82352864056de98c21f42fc4d2031; original global index 4636.
def localCycle00086 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 3c760c4889a6dce330c97de5985a1b4f9e7f129d78674866f6eff2c58cf0782c; original global index 4689.
def localCycle00087 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 3 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 21 1, .gapLower 6 3, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 3c7642c05f8c452eb77f04c59c56d9f9bb025377660276799f8e4530d33cde8d; original global index 4690.
def localCycle00088 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 33 2, .triangle 11 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 3c8d570ceb6d4bc66a4bb21a00c7b5dca165c9dc3b1e4019a70a0d39c055348f; original global index 4696.
def localCycle00089 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .triangle 4 2, .gapLower 6 3, .triangle 27 1, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 3c8fa76e1eb037596aaa547a936fa82c42a1704b4af169a0e93a1448c99396ea; original global index 4697.
def localCycle00090 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 3, .distance 0 1]
    constant := ![2, 0, -2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 1 1, .triangle 4 2, .gapLower 0 2, .gapLower 0 1]

-- Original cycle 3cb3232bef2c5e86e7cd7249056cbe2ba31d942d4adeebc702c46ab6e2081721; original global index 4709.
def localCycle00091 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -3, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .triangle 14 1, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4]

-- Original cycle 3f364ac975d371ad94524175a1dde8198b5e0fb11459cc03d8a87aac708c75fb; original global index 4880.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![4, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 19 0, .triangle 21 2, .gapLower 6 4, .triangle 8 1, .triangle 27 1, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 3fc63d7ba51a08a684f92211372d150ab5028fbf9891eb1f76f306025a8f1396; original global index 4926.
def localCycle00093 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 3 2, .triangle 14 2, .gapLower 6 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 41759978cc876fcc205da5a92a69f145e16f6f9ec142697509c1ffa724673cfc; original global index 5050.
def localCycle00094 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 3 6, .distance 1 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 21 2, .gapLower 6 3, .gapUpper 3 5]

-- Original cycle 429190913187aba8b2f516215e17c3a74017936accca3ad90bf55d7f8d9a6446; original global index 5128.
def localCycle00095 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 42a9e4de31121ff103c753e84bff9734a72b5933dbc562c19f15c427092190a8; original global index 5133.
def localCycle00096 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 42e57fe5a431b2a503a44f28ce592d5042bb19dacc4efd972c8fd3227d6ba9ca; original global index 5151.
def localCycle00097 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 42f30855cf380e249c4f8cd58958ba13c1ae5141c1ae0cf73b3398827448b763; original global index 5157.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 12 2, .triangle 14 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4]

-- Original cycle 4361043f128e3247d13bc9d3fa0effff24519123073daa695fc35eeeb0dd7e96; original global index 5201.
def localCycle00099 : Cycle where
  length := 12
  data := {
    node := ![.theta 0, .distance 0 2, .distance 2 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 1, .theta 0]
    constant := ![2, -1, 0, -1, -1, 0, 3, -1, 0, -1, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, true, false] }
  origin := ![.gapLower 0 6, .triangle 8 0, .triangle 29 1, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .corridorUpper 1 3, .triangle 21 0, .triangle 32 1, .triangle 9 0, .triangle 1 1, .gapLower 0 0]

-- Original cycle 4456ee5e08c14b1bc941ad5357b891bba9f08d9f740fbed321f072c74f98cbbe; original global index 5291.
def localCycle00100 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 2, .triangle 4 2, .gapLower 6 1, .gapLower 6 0]

-- Original cycle 44d587229dd103948fe2aa7eb878bb732dff99c8c2fac0b543baaf13ab65c920; original global index 5332.
def localCycle00101 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 27 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 460b2f8d3e4b44e7884c70f5c4bf3eb55800e64555836f84c54c90385aa82081; original global index 5420.
def localCycle00102 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 4701bc272c2086577a7f692ab4d5ea38e940ae34c5a7890395b3e1f5ce4aae32; original global index 5501.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 6, .distance 2 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 2, .gapLower 6 3, .gapLower 6 2, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 49ef9af243a4b915298f60d04cf4a7ed1515056385b33f63b6db7500405089bb; original global index 5737.
def localCycle00104 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -3, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 21 1, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 49ffaf5f8bfc15c474b5fd80ae74b99c24111c59160dd6f1f242e4443ac3e723; original global index 5745.
def localCycle00105 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -3, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 6 4, .triangle 27 0, .corridorLower 2 3]

-- Original cycle 4a7cc3bc807662c612aa42a2c33eb252d45a3bf4e3f62e268ceda4ca12df1e2b; original global index 5775.
def localCycle00106 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 3 2, .triangle 14 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 4ab6b192ce633be83f797bfc9027ea24c83160c7864ad12b67645b1c415042d4; original global index 5796.
def localCycle00107 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 33 2, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 4aeab57e1a27a17405443f1e8b99b46ee72993c2dc9b3aa89449fc64a3cf6c41; original global index 5817.
def localCycle00108 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 2 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 33 2, .triangle 11 2, .gapLower 6 2, .triangle 29 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 4c0bd19fb4c2935789e621e6c8904dce8e9978ebb88e8abba5d88e6d633b68b7; original global index 5902.
def localCycle00109 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 3 6, .distance 0 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -2, -2, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 6 3, .gapLower 6 2, .triangle 8 1, .triangle 30 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 4c0dea0ea7252b77de6f9bb4380609018ff5af1630854e5d8ad0e74dca622da2; original global index 5904.
def localCycle00110 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 0 6, .distance 0 4, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 11 2, .gapLower 0 4, .gapLower 4 2, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 4c48167e107b1cd5a45a2b230d56483df3d89efce7895d8bb2b11bf83467349e; original global index 5921.
def localCycle00111 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 4c6e7c12445f13b5cad1d317194ef7f5b5c03135f907af01f300b1ef11369ceb; original global index 5934.
def localCycle00112 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 29 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 4f4a228b056634bf7bc3e4b840d9f77e8c0a85a1f1435081f34ec58be9858c56; original global index 6162.
def localCycle00113 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 4fb6edf5c20d2771e5c0fe364d38c83cce9d0976bdae39be84d58a6110455a75; original global index 6190.
def localCycle00114 : Cycle where
  length := 3
  data := {
    node := ![.theta 5, .distance 5 6, .theta 6, .theta 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 0, .gapLower 6 0, .thetaNext 5]

-- Original cycle 500e918d2777721da7414b2f50ca59106ae992e333404ed0d7068c72c190ae7b; original global index 6214.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 50461e2cbb2d789fb099ce48fc1d2c00d458edf1035df0e1e387984205eb6792; original global index 6231.
def localCycle00116 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 3 6, .distance 1 3]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 21 2, .gapLower 6 3, .gapUpper 3 5]

-- Original cycle 506a36aafc5e84b6423e3b9413932b33d83bd22c635924b03cbc2f119f3c2b8d; original global index 6242.
def localCycle00117 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 3 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 1, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 50e227e1dd6a5b5ca77b88b38f21113c051921140f156df6ec7cb75e8f7d1a0a; original global index 6282.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 512154935926d5d99eec38d5e00f16ec1df3d426d7a57e8cf75b354b3d3fb815; original global index 6300.
def localCycle00119 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 24 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 519a0f687a56230423bbc07655dcfb4983740d48f4ef801b8d525f4265426f1b; original global index 6349.
def localCycle00120 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 21 1, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 52ab866aacf7887e45da17144cde3b1fd5cc895ebb61c59e33dbfd44a174f98c; original global index 6425.
def localCycle00121 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 54a2601f2200475c218aec4a59b9cfcfd0a51e21f719150ca4aed3538d9fd943; original global index 6557.
def localCycle00122 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 2, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 55059abd8a72c807ea8becb9e89a0717737d623fc99e39b05b9b6303ad3c153c; original global index 6584.
def localCycle00123 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 6, .distance 0 3, .theta 0]
    constant := ![2, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 7 2, .triangle 12 1, .triangle 13 2, .gapLower 0 2, .corridorLower 0 3]

-- Original cycle 550eaff94b0a7e3f713574bf8c67f5457d91f49196750be14d02b2717185455a; original global index 6589.
def localCycle00124 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 5533750f3458e5c847d0ea1c936c4984e20e83370994b7143421c70dfdd30921; original global index 6596.
def localCycle00125 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 31 1, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 5594682ef0e10b7c176d48e0e49e868f3c7bc9101f7804669420919153cb0a2d; original global index 6633.
def localCycle00126 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 55f0f3d99a61657813fb5295caae2ebbf57d392bef5a9c063b75d39b210da6d6; original global index 6663.
def localCycle00127 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![4, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 0, .triangle 27 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 57580d43d59e8c4721e82c434b098ede0f6e2c3e95fd839759367439c3aafe10; original global index 6771.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 32 0, .triangle 29 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 59b2967264f901cc1d6f865b132f82919ffc7c7efd2df32f9f105a35a54974b5; original global index 6979.
def localCycle00129 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 2 6, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 1, .gapLower 6 1, .triangle 30 1]

-- Original cycle 59bf7242e6e0328066dfb8413a5dd11ed82ad700e135a38c88ee123c399f0499; original global index 6982.
def localCycle00130 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -2, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 21 1, .triangle 20 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 5a44bf134757bd85e0d0a4f53e2461d511431a13bc7a91aa346f0a99418bfdea; original global index 7023.
def localCycle00131 : Cycle where
  length := 5
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .theta 4, .zero]
    constant := ![0, 2, -2, -2, 0]
    coefficient := ![1, 1, 0, -1, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .gapUpper 4 6, .thetaLower 4]

-- Original cycle 5a541385aeac04fc01f9b5dd00d87e4f3ea299119729d38a76e3b5355eeeacca; original global index 7029.
def localCycle00132 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 25 2, .triangle 29 0, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 5a62c2d8a4e119c7b10b109e9d58623b2a711d54dea7eb494ec66e2e6b83b267; original global index 7034.
def localCycle00133 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .triangle 8 1, .triangle 29 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 5a83576420b0cf4f73f6fe7d7485f544743986a29c36005d8a0af3c971e14366; original global index 7046.
def localCycle00134 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 6 4, .triangle 27 0, .corridorLower 2 3]

-- Original cycle 5b1834896617a83f6cb2f1d1f0859abc4ec7bfd3ee0344279a858d6eb143f214; original global index 7089.
def localCycle00135 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 5 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 24 0, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5b2ac214a60d3e628b8735f4f92b738e1e0eeeff47ef4eba4785fec48f945b36; original global index 7097.
def localCycle00136 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 24 0, .triangle 30 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5c3ecec023570ace9d4fcd7651d844cef3148c3450d8dbe99a0ceda6460f1154; original global index 7182.
def localCycle00137 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 2, .gapLower 6 2, .triangle 14 1]

-- Original cycle 5cbd840771248fe8e7928e8b03307a801c603f38f661302130503e0fe0af3d78; original global index 7216.
def localCycle00138 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 33 2, .gapLower 6 3, .gapLower 6 2, .triangle 27 1, .corridorLower 2 3]

-- Original cycle 5ce85879f85be926e80172626ac35b590a1735b2ea6381e97076be48d68c56f6; original global index 7233.
def localCycle00139 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .theta 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -2, 2, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 2, .triangle 14 0, .triangle 30 2, .gapLower 6 0, .gapLower 6 6, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 5d026a53a560a5a5a767b1175641f5e383caf7a93f77e3897416681de7260696; original global index 7236.
def localCycle00140 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .gapLower 6 2, .triangle 8 1, .triangle 29 1, .triangle 28 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle 5d684c6d21f1c03e94204f2e7757d95371b04dbbdb0cb7c1180039cdd80b0c74; original global index 7270.
def localCycle00141 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 32 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 5e61cb079ef0ccf857c0f0af5b7f81f9f2cbdb27fc4b617731286bb9bf001746; original global index 7343.
def localCycle00142 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 5e9f6d8560b059b5c7a525e18a923a0084a514ca995e33e28762551fd419665d; original global index 7361.
def localCycle00143 : Cycle where
  length := 3
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 6, .theta 0]
    constant := ![2, -2, -1]
    coefficient := ![1, 0, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .corridorLower 0 6]

-- Original cycle 5f1ded490acd0c795281546231f9fcfcaf3fd2e54317ed0b70ded380930b0ad4; original global index 7408.
def localCycle00144 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5f57a43b550d4e658c63f25de3fc411fa1de98a5b94850f6f08c2cfbc01ebf04; original global index 7423.
def localCycle00145 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 6, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .gapLower 6 2, .triangle 8 1, .triangle 27 1, .corridorLower 2 3]

-- Original cycle 609cb687f53a157afe1f858b91f42d8676b645c5c6d578988cf5fcebbcfe0235; original global index 7522.
def localCycle00146 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 3 2, .triangle 14 0, .triangle 30 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 60de08d2fe44f8ee455d8901cc6b979833738ccff879df4bd5fe793a119b59ee; original global index 7551.
def localCycle00147 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 5, .distance 5 6, .theta 6, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -2, 0, 3, 0, 0, -2, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 0, .triangle 30 0, .gapLower 6 0, .thetaNext 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 21 1, .triangle 19 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 618d83943194cdc60c3f4f4bf402aae3a54c8a145abfcbd2a410bdfa8c7e9758; original global index 7610.
def localCycle00148 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .gapLower 6 3, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 63accf731d23d65d7cad6c62c0e711ce28478acebddf75065445f0f1fee1d17f; original global index 7768.
def localCycle00149 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 9 2, .triangle 13 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 642dced0cb4af03f62172a2d4efbfae8582047f22f314d4f1269b485a931e247; original global index 7806.
def localCycle00150 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 0, .triangle 28 0, .gapLower 2 2, .triangle 27 0, .corridorLower 3 6]

-- Original cycle 65fea67d01f7780b3403e22f83ae1d7e7cd59321473f2f059475b00834b24c70; original global index 7937.
def localCycle00151 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 0 2]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 5, .gapLower 5 2, .gapUpper 2 4]

-- Original cycle 6633dc2eae4ee3ad3dd2505adeb8241621238b1094b978717ec9fdb115339158; original global index 7949.
def localCycle00152 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 21 2, .gapLower 6 3, .triangle 8 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 665e99bb1dfcc15841593be863142484a0caa58fb18d4bc6a660c7a6481642c0; original global index 7960.
def localCycle00153 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 5, .distance 5 6, .theta 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -2, 2, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 0, .triangle 30 0, .gapLower 6 0, .gapLower 6 6, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 67b258f334448a9f79830ae35c91b735994f4f576d6b8ebb89407743f3682b54; original global index 8053.
def localCycle00154 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 6 4, .triangle 8 1, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 68eca1f9bf833863b485fc69ae154914d6bfe719695174a10ad7ebb030918d04; original global index 8163.
def localCycle00155 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .gapLower 6 3, .corridorLower 5 6]

-- Original cycle 690b874cb659bf587070ed2072d95b1f25b419d152bf45ea519a6fc817fa6426; original global index 8171.
def localCycle00156 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 698d3164e381d7cbd0c6ecf84cdcf2a1b5dd4803702fd9652afbf4de57f8855e; original global index 8208.
def localCycle00157 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 32 2, .gapLower 6 3, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 6a9f9c86b2ba1287f12670287cf5fa2572119edeac940393a3ee9db01f6b6760; original global index 8302.
def localCycle00158 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .gapLower 3 3, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 6b65350f2e2225ca61df173af6a48c20896d1251c130c7475f9e272287754662; original global index 8360.
def localCycle00159 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 6 4, .gapLower 6 3, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 6e700030893f7c6db3d7397b3be4bec96185911c0143a992c9b83f3b7748b201; original global index 8570.
def localCycle00160 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 1 6, .distance 1 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .triangle 21 1]

-- Original cycle 6e82079550108f08811f830682a83d77c4fefb7ed8a705555f539e1cf0e577df; original global index 8575.
def localCycle00161 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 4, .distance 0 6, .distance 2 6, .distance 2 3, .theta 3]
    constant := ![3, -1, 0, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 31 1, .gapLower 4 3, .gapLower 0 3, .triangle 8 1, .triangle 27 1, .gapLower 3 0]

-- Original cycle 6ed6ad907eeb398ae3223f213e2d019e3c347af9edc6c5fc324b57d029bc5e77; original global index 8599.
def localCycle00162 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 0 6, .distance 0 4, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -3, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 11 2, .gapLower 0 4, .gapLower 4 2, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 6fb7cdd5d699ecab49e512c6c2327b41fcb91c25f401b37fda6a8fad5cdb4983; original global index 8667.
def localCycle00163 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 1 6, .distance 1 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 5, .gapLower 6 3, .triangle 21 1]

-- Original cycle 701018385ce293b99992b1371a1d0adb3e163c733ee45ce8a485c9f7f94a66ab; original global index 8686.
def localCycle00164 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 5, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .gapLower 0 4, .gapLower 5 1, .triangle 26 1, .corridorLower 2 3]

-- Original cycle 7054cb3f0417e17d8ae1f4c0332c458c72f607e2a8660cb010caab02b41f5611; original global index 8702.
def localCycle00165 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 24 2, .gapLower 6 3, .triangle 14 2, .triangle 8 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 70a4d6ec3dcd58f512f6f71b4e24a6aa9561a5a3edf3e7e0acb1213274089efb; original global index 8727.
def localCycle00166 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 13 0, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 70bba30de177614fd786012efffbe4f3efb3b3a66c371c055490c2615c494e0b; original global index 8738.
def localCycle00167 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .triangle 2 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 715d15ff0f5412da2daa6c1b4787be0b835f6a52e9b3482d0f98aba6b4b2515b; original global index 8793.
def localCycle00168 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 11 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 716875c090e20ca65dcfaa41f3a15d254d86d41496a76386879ffe9bc21385b5; original global index 8800.
def localCycle00169 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 34 1, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 7183b8b8099836465ced16c26a3c0b93ec00c47e61b6dab79630b02fe7fcf006; original global index 8809.
def localCycle00170 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 2 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 27 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 71aa875f00b639aa823303868b7dd2c33a559cf1c434cf17413f2a8cd2e3abff; original global index 8820.
def localCycle00171 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 32 1, .gapLower 4 3, .gapLower 0 3, .triangle 3 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 71f58f98e99dd0cd2bebc76d8a51d758cd2fbb729acf4bf4d864fd11225a7049; original global index 8831.
def localCycle00172 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 1, .corridorLower 2 6, .thetaLower 2]

-- Original cycle 75081e737a70b932f1cec7de22a6a2a567c8405203897b77c170765e1c17a822; original global index 9070.
def localCycle00173 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 7536d3d71df16bc843111da1f305a143ac83519db4636fdc70b8b580198e3f72; original global index 9082.
def localCycle00174 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 21 0]

-- Original cycle 7660a91bcc9db1900631003d3bc5d9a5aa5922bc61767fafebe430a534e868fe; original global index 9163.
def localCycle00175 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 3 6, .distance 1 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 21 2, .gapLower 6 4, .gapUpper 3 4]

-- Original cycle 76abde22bd33dc522960d4b06f60cd431a1c466fe273152418302caff2873c78; original global index 9186.
def localCycle00176 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 7700c4bac468d5d97a0a17226d13450fdf1107c73b488a7c8c863b6afed60116; original global index 9211.
def localCycle00177 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 7708d37157435868b9953a8af2e6c6a39dc09ce82619e492795ba8e56fb6d544; original global index 9216.
def localCycle00178 : Cycle where
  length := 5
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 13 2, .triangle 8 1, .gapLower 6 0]

-- Original cycle 7860d8f96c6bc437356b833a42c46d2ed78622f42343d7fc7b986d02e986c488; original global index 9307.
def localCycle00179 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .distance 4 6, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, -1, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 7 0, .triangle 28 1, .triangle 29 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 790a1ada8f939ad285b33d97054e2c6f621773753648de134fc660230bc84580; original global index 9366.
def localCycle00180 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 3 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 79862d64faca80ca4a46b2b5aa8c80eec5797c8e408832825225d36fb3bab1f4; original global index 9401.
def localCycle00181 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 33 0, .triangle 30 0, .triangle 26 1, .corridorLower 2 3]

-- Original cycle 7acec9894961ccc8dee829623406f4c62d94655a0d0823428fdca99e4fa5667e; original global index 9507.
def localCycle00182 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 3, .gapUpper 4 5, .gapLower 6 4, .triangle 21 0]

-- Original cycle 7b5004ce38c5217fa9a2f71287a77a9dec5ecad25c277fe4d9ab7755144f6949; original global index 9549.
def localCycle00183 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 29 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 7b775569507c208f37594f4463894cbc187c20392b8e327c45304c812ba12265; original global index 9555.
def localCycle00184 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 4, .distance 0 5, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 2, .gapLower 0 4, .gapLower 0 3, .gapLower 5 2, .triangle 26 1, .corridorLower 2 3]

-- Original cycle 7cc4b4752b8c8798135c46aae83e3eb87848a843fc3d5724379affac01fc0d89; original global index 9664.
def localCycle00185 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 7cf406f6ff441e3075d96664c9abe72b276e1021ad514254581a058e097335b3; original global index 9675.
def localCycle00186 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 7d9ed5ab4fc9bc887032485bb95226012bd3fc3bd9df0308a486ddd422039bdf; original global index 9750.
def localCycle00187 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 6, .distance 0 3, .distance 2 3, .theta 2]
    constant := ![3, 0, -2, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .triangle 12 1, .triangle 13 2, .gapLower 0 2, .gapLower 3 1, .corridorLower 2 3]

-- Original cycle 7df73e0df0351bc9092fa21d71f96ba55b9e4b46840858c70346d367137e1250; original global index 9782.
def localCycle00188 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 7f23c280d610129ed79b2fde0e45b79a3a86ba919efb237b70cb5f350efb6169; original global index 9860.
def localCycle00189 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 7f691e214d443174fec35365c39e557f26a7b93253f60e33a81a1b9113c34510; original global index 9881.
def localCycle00190 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 3 6, .distance 0 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 11 2, .triangle 14 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle 7f7a4539c1c9042eb980f4838782750652572741411db58ae00fa36aea94d3a7; original global index 9888.
def localCycle00191 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 34 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4]

-- Original cycle 80b6320b87b7494c2643f79e2fc2d204708f8a11ea215f490c546ab5990fea78; original global index 9995.
def localCycle00192 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 3 6, .distance 3 5, .distance 3 4, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 21 1, .triangle 33 1, .triangle 31 1, .triangle 9 0, .triangle 5 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 80f953ba862b15220765b3dc6d2f50d4e0b1dde8462d2010d1cbb918c6699d6b; original global index 10009.
def localCycle00193 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 5 4, .triangle 10 0, .gapLower 0 1]

-- Original cycle 8147cec10cc223b217b34766337bb4b01dd15435bdd06c531a59729c740753c0; original global index 10038.
def localCycle00194 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 3 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 5 4, .gapLower 5 3, .gapLower 0 2, .gapLower 0 1]

-- Original cycle 82c5506aacd9855be3d83c522f18790997bbe2280657c619ee73111085acdf06; original global index 10144.
def localCycle00195 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 837d298dc97fa3f8bb75d72a6420e903e2e51c62f3e0417b74b977919db73936; original global index 10203.
def localCycle00196 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 83ae9c7e2bbc89454a98b3447bdccf765b73bc4d9b249d5720d5d8fd1bd4adf3; original global index 10220.
def localCycle00197 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 842ad4f7d29822d620ab1396ff0d71f60ba1c5fffa8a755a482a2509ba6d6242; original global index 10261.
def localCycle00198 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 32 2, .triangle 11 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 845f95f94712760cdd01479b53e221847be395da635bf44c1de65e90a1ef1bd6; original global index 10281.
def localCycle00199 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 88d093fac692905103876df9787e3737957281370bfef62832f8cd2f6aa92e4d; original global index 10598.
def localCycle00200 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapLower 6 3, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 899c1439127d922d72b3e69c7106fa6dce63bdce123a3b87f411564e02794893; original global index 10657.
def localCycle00201 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 3 6, .distance 0 6, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 6 4, .gapLower 6 3, .triangle 8 1, .triangle 27 1, .corridorLower 2 3]

-- Original cycle 89b059826cf1bef92ad9bd8114a149c630d0ed88aa7e6da2e1ef81c0bcc91c89; original global index 10667.
def localCycle00202 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 23 0]

-- Original cycle 8b6cdc580d9f2e0760583179f59581a02e48be74a9570b1795e8800e98f51290; original global index 10804.
def localCycle00203 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 5]
    constant := ![2, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 21 2, .triangle 24 1]

-- Original cycle 8bcb4af9a1e84ef6f3055985d1089ad1214c968837bb6e08059e80f8bb74175d; original global index 10824.
def localCycle00204 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 27 0, .gapLower 3 0]

-- Original cycle 8d38f7e2498f521e790a210601c8097f6b5801cebaaf72ef9703d8ec79df7a0d; original global index 10918.
def localCycle00205 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .gapLower 6 3, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 8d465f71de88a4cde4ea1793ce0568f65a3afe2727401b9c389ef33ebd24d278; original global index 10923.
def localCycle00206 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 32 0, .triangle 34 1, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4]

-- Original cycle 8e21607e4fa5321de8b97cf21c0418b310af6669d3145df745b0263b78b49c59; original global index 11008.
def localCycle00207 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 6, .distance 0 3, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .gapLower 5 3, .gapLower 0 4, .triangle 13 2, .gapLower 0 2, .gapLower 3 1, .corridorLower 2 3]

-- Original cycle 8ead36a71a8a99af5943501e9ba54b0d2be55f7f2d0b248bde619ac49d9b75db; original global index 11040.
def localCycle00208 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 8ebad7ab44573f06b83e943ebbae836831800dc62bb2ea6a7688d04f2b113815; original global index 11044.
def localCycle00209 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .distance 0 3, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .triangle 9 0, .triangle 5 1, .corridorLower 2 3]

-- Original cycle 8fec0e9d06bc599f934a107b04e08f04188163d6c24e5322b72a43baae77f086; original global index 11139.
def localCycle00210 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 6, .distance 2 6, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -2, 2, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 11 2, .triangle 8 1, .gapLower 6 0, .gapLower 6 6, .triangle 34 0, .triangle 22 0, .triangle 19 1, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 90ad334d0c9064581fa51da984efe3c91133f66714921757f5cc4a992f38e688; original global index 11203.
def localCycle00211 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 911140bf285ac46d209204a634e7d0bfe50236f1efc4b69d9c427aa474d9eb42; original global index 11232.
def localCycle00212 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 2, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 21 0, .triangle 19 0, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle 919d099d7026aaf28667f74b596815647777812000e2b56481c6e18a61f7a6ef; original global index 11284.
def localCycle00213 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 32 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 91e27c9a00d9209d6114268e8b099d720f9a6d1f23415562966d5476a730a754; original global index 11306.
def localCycle00214 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 6, .distance 4 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 29 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 933bee6d35c87bb10c37f2ac218ba018d02ea5ee33b1a87012d525421b7dae98; original global index 11416.
def localCycle00215 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 9 0, .triangle 5 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 935eaeb414d65cfd77a988f439947ba6367e6a4768a9e25b7e26726211712e47; original global index 11429.
def localCycle00216 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 1 6, .distance 1 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 24 1]

-- Original cycle 9463bc8f8e4267305ec789c7037bbe68134a4b1ba01e4d22e58832dfc6e53d2d; original global index 11516.
def localCycle00217 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 4 3, .gapLower 4 2, .gapLower 0 2, .gapLower 0 1]

-- Original cycle 949f499d382636b825ea5e3b1f99adac312948189d01b5c07f77dcfc75c9c9ff; original global index 11532.
def localCycle00218 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 24 2, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 953e8c21043e6a5d896c9dabb8399b4b7eeb46af07fa031725fa48c84fe02edb; original global index 11594.
def localCycle00219 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 2, .gapLower 6 2, .triangle 8 1, .gapLower 6 0]

-- Original cycle 956a9c33de239974294df9d8bae039ed6c77424a0382d5c61b4061f78c7bcefd; original global index 11613.
def localCycle00220 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 0, .triangle 19 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 962907bec5300d3d4fdf5f051c873dc91a9afa8f458478fefc8044cf0e72dee6; original global index 11674.
def localCycle00221 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 3, .zero]
    constant := ![0, 3, 0, -3, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 25 0, .gapLower 3 0, .thetaLower 3]

-- Original cycle 9647bf5cb88ccd71a587ff1e9376223fb8ac3a8fdb1c694968fda980f4fe2d47; original global index 11685.
def localCycle00222 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 96ab70f24a5cf79c633a5a6ead5763726717e8039bd9860bfab8b688b2d26c9d; original global index 11713.
def localCycle00223 : Cycle where
  length := 4
  data := {
    node := ![.zero, .theta 1, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -3, 0]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.thetaUpper 1, .gapUpper 1 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 974a48c85bacd06feee5aae933afca62aa50cbf0047d50a03a7102772a1e1be1; original global index 11757.
def localCycle00224 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 97c3a3ab110bead9878dea8dded3b0f827054e1e9b3dad5d471ec3ba66af0a7b; original global index 11788.
def localCycle00225 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .corridorLower 2 6, .thetaLower 2]

-- Original cycle 97ece87445c15ead48a72a9cc43ea966be2bb91555ab6e31c9a1560ab6844b97; original global index 11798.
def localCycle00226 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 982e886df5c3ec4a2f2284a167f816180587478cb4ddb7dd05c76f653ae9d0d1; original global index 11821.
def localCycle00227 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .gapLower 0 3, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 9832328869998c93d1204b28c2b29e18ef355e696ed04e87e8af14787cd1e880; original global index 11823.
def localCycle00228 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 993190166bd53d381734bb7f4219137a20a1deaf4e01819a6493b1853cd5a824; original global index 11895.
def localCycle00229 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 5 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 0, .gapLower 6 2, .gapLower 6 1, .corridorLower 2 6]

-- Original cycle 99f4d6b13c1c5c464270d5808d97f6b2fbc2bf7bc2dcdaff478ecef7b3e4c434; original global index 11953.
def localCycle00230 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 9aa1f35f34276693656a6ca5934a71bec069b9623b9903594df5e74c5265d6e7; original global index 12014.
def localCycle00231 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 9c37c7afc314edc725df194e43a992704d6254fea3dd106c6e90f65e47e6e463; original global index 12155.
def localCycle00232 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4, .distance 3 5, .distance 0 5, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 31 2, .gapLower 5 3, .gapLower 0 2, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 9c5abe9570441e8ff7d3d5909743d5a2efe350bc49e2c404cc4a4772ff0dab7d; original global index 12163.
def localCycle00233 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 32 1, .gapLower 4 3, .gapLower 0 3, .gapLower 0 2, .gapLower 3 1, .corridorLower 2 3]

-- Original cycle 9c80c84c3c3326c3acc40e823977da357e8540e1b5c36ccf84afeca27079a132; original global index 12172.
def localCycle00234 : Cycle where
  length := 5
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 2 6]

-- Original cycle 9da233d89473850126f57d7b5f991b5a1d6fd207da3b2776e8a518ce87e28346; original global index 12259.
def localCycle00235 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 6, .theta 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -2, 2, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 0, .triangle 30 2, .gapLower 6 0, .gapLower 6 6, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 9e143836cae4d94368dd3a9796942d9e029fe3a418b2ebc5eff801f71f5491a1; original global index 12302.
def localCycle00236 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .triangle 8 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 9f172cca317899bf9100c0200b452f160ed49f936b41c7f1802eaaa4d96898c6; original global index 12390.
def localCycle00237 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 23 2, .gapLower 6 3, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 9f903d5951f4fb2920a2d2aee9ad41d27d235a5d0a4da25fdecc40b510ae1edf; original global index 12417.
def localCycle00238 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 9fd543e4f0a8276b2a6bf1ec281112e9b287b1efed8293ac1c1f627dc677106e; original global index 12442.
def localCycle00239 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle a03ca4b805b62aaaffda902d53dfb63ebaa8c6351d9c7d6958251e2ba47eed69; original global index 12466.
def localCycle00240 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 1 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 24 2, .gapLower 6 4, .triangle 11 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle a5e7b716effb3fa3344c219635b1bbd54dbee4a71345a97d09e37592387692dd; original global index 12888.
def localCycle00241 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 4, .distance 2 3, .distance 2 6, .distance 3 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 27 2, .gapLower 6 2, .triangle 33 1, .corridorLower 3 5, .thetaNext 2]

-- Original cycle a6a9c4a8a671fa8fa69e77aedc99d5b4286883a525a2fa8434d6e926e9b05560; original global index 12949.
def localCycle00242 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -3, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .gapLower 5 3, .gapLower 0 4, .gapLower 4 2, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle a6e190e0947da10e2e368a695c7ae7078d5ee7da532efb521cd927ed599c5281; original global index 12960.
def localCycle00243 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle a6f85dd20e1b4054fca47cac0d34831b1f9e190590bce0710798c68b846d8d10; original global index 12974.
def localCycle00244 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 3, 0, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle a761f6d7e0662ccc5d19c332394b913137771b521da4ce5649db9a88b682e941; original global index 13022.
def localCycle00245 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![4, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 11 0, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle a764d99857cd2ce15ed10ce5a8026f0748a19e3d5e158d6990930b73c51f6368; original global index 13024.
def localCycle00246 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle a7ec18660522310b3e75bbd7dd5b412e4e5feed2c4760cf30c445c9f243a4189; original global index 13072.
def localCycle00247 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 10 2, .triangle 12 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle a9033dfb080fb38188be307c8e7337ceea072c5a715298781e13ca684d4c7c0e; original global index 13157.
def localCycle00248 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 3 6, .distance 0 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, 0, -1, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 11 2, .triangle 14 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle a967eb48a2cd3c85f30d18a6dd36e7910f0ea8e16dc927913762dcdce53f8015; original global index 13188.
def localCycle00249 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -3, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 6 4, .triangle 27 0, .corridorLower 2 3]

-- Original cycle aae0c5c8df2e8752097614342e7f4855a12bd70d60a73409ce54b0d96de574d1; original global index 13311.
def localCycle00250 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 4, .distance 2 4, .theta 2]
    constant := ![3, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .gapLower 0 4, .gapLower 4 2, .corridorLower 2 4]

-- Original cycle ab2be0bf01656099b186eecaba07962761b9325785a1ae9803d238561d32d329; original global index 13333.
def localCycle00251 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4]

-- Original cycle abdd6696584bdc9aa97ba8f87d2154e3130cfa436d5a5a3e342eb432da1282c0; original global index 13384.
def localCycle00252 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapLower 6 4, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle ad5dec974d8d48cef06ed4ed5921497fa22d1f2beff281714d9407fefcf9cb2d; original global index 13521.
def localCycle00253 : Cycle where
  length := 4
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .theta 6]
    constant := ![3, -2, 0, -2]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 29 2, .gapLower 6 0]

-- Original cycle ad6caedbcfefe9983cc6ff696c89613f8c49d6c4abdd60168af22b6facbcc178; original global index 13531.
def localCycle00254 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle adbb70aaa150b54f001466e33b79975d3bee8674330f5281068797f5609c78fe; original global index 13560.
def localCycle00255 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .gapLower 3 3, .triangle 9 0, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle aee9e779b884d18665df30a271d5d9c27544654033b7927c4075e30bf82becac; original global index 13654.
def localCycle00256 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -3, 3, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 9 0, .triangle 5 1, .corridorLower 2 3]

-- Original cycle af300f3a6ab9ed247c4d1d62567477b63a937d39c0218c613767d5b63c9b2ef8; original global index 13684.
def localCycle00257 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 5, .distance 2 6, .distance 5 6, .theta 6, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -2, -2, 0, 3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 0, .triangle 30 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle af80b9228b17629cab283e0a4c1c8195569772000a2034e95203dd226ffd6e52; original global index 13705.
def localCycle00258 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle afad22422a46f5c04391aaac65fd47e14a764d2bfb45bbb899f38fd01d34b295; original global index 13723.
def localCycle00259 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![4, 0, -1, -1, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .gapLower 5 5, .triangle 20 0, .triangle 21 0, .gapLower 6 3, .triangle 14 1, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle b12f6ac07326099ba8ba0b719c3caeb35878b27c8fd15e0b8eeb50de5c6feb57; original global index 13838.
def localCycle00260 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, 0, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .triangle 4 2, .gapLower 6 3, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle b237e967e4210ac44060c47b9bda58305168ae1225d7e8662f6417471794801f; original global index 13926.
def localCycle00261 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle b28279ea74596503bcbd0609f6294f13ca26bcec1e31770028cb2349bd52acdb; original global index 13946.
def localCycle00262 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 3 5, .distance 0 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 10 2, .triangle 14 0, .triangle 34 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle b28dd85bb2d34b7ad776431ea0f0ad58d05e02826a881186f854039021d60df7; original global index 13956.
def localCycle00263 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 33 2, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle b2effe6c96f039c16d152cdc607890cdb5f4fc9ec7442392ae0f88ae69cc9a50; original global index 13985.
def localCycle00264 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 5, .distance 5 6, .distance 2 5, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, 3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 10 2, .triangle 14 0, .triangle 30 0, .gapLower 5 0, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle b3705f500e628e69afece0b6f0e3e687eba79696a6b02c3f6ea7d42f42cca100; original global index 14023.
def localCycle00265 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle b37920ba1379298dda77e28a4a63b6f4a63257a4e1e71b654a563faf9c19488c; original global index 14025.
def localCycle00266 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![2, 0, -1, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 4 3, .triangle 9 0, .gapLower 0 1]

-- Original cycle b45479689e23feee5882f0cd949e17ae3928104316c843d77ce65fef57b64d6b; original global index 14086.
def localCycle00267 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle b46970a2fb60275c75e192e02a9d1728bd6e7680cb9c8d38eb0521c13a5893ec; original global index 14094.
def localCycle00268 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapLower 6 3, .triangle 14 1, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .thetaNext 1, .thetaLower 1]

-- Original cycle b4d0696e008bb989524fd06562b2482a675290c28df002494b75f0d309ca1088; original global index 14119.
def localCycle00269 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .gapLower 6 2, .triangle 8 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle b4d9ac179e5c66e769dda42b7b6ec26dd394421f0e270f89ddd0dd857dfe5174; original global index 14124.
def localCycle00270 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 2 6, .distance 5 6, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 30 2, .gapLower 6 1, .gapUpper 5 1]

-- Original cycle b54de0cc6a0ef6b1fbe1d769355870a05924d9a3d6ebc221d755a6f4276719e2; original global index 14164.
def localCycle00271 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .gapLower 6 2, .triangle 8 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle b6273b4056f9c486d4a31df4a9c50cbf7a0f71714a842f083e25e8eacdf57e4e; original global index 14225.
def localCycle00272 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 3 6, .distance 1 3]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 21 2, .gapLower 6 4, .gapUpper 3 4]

-- Original cycle b669f99f18700681adc13b3465108b06bc81180ea8d40e4b3abccb8440ce3fa0; original global index 14256.
def localCycle00273 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 7 2, .triangle 14 0, .gapLower 6 1, .gapUpper 2 4]

-- Original cycle b6b26966a16520079173ca473693f4fe3705f606931ec363a84784a1c2471389; original global index 14279.
def localCycle00274 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 2 6, .distance 2 3, .theta 3]
    constant := ![3, -1, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 33 2, .gapLower 6 3, .triangle 8 1, .triangle 27 1, .gapLower 3 0]

-- Original cycle b6bd74a2439684cb9854f83b852c27335755457c14423eaf2c3f98c3a8b45441; original global index 14281.
def localCycle00275 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 23 2, .triangle 4 2, .gapLower 6 1, .gapLower 6 0]

-- Original cycle b7f6deb820e0f0a74c016dee75b85f5d2f90fd1a193d96b7513c7b47c02ee84d; original global index 14354.
def localCycle00276 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -2, -2, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .gapLower 6 2, .triangle 30 0, .gapLower 2 2, .triangle 25 1, .corridorLower 2 3]

-- Original cycle b8168c5549051cc4d62dcc3073b391dcdc4da49a127c1ba85b74548a3144b8ca; original global index 14361.
def localCycle00277 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle b8242679a3d8e93b7fa15f68558b7c6ff6bd23eb464d01296f6d06acdd013278; original global index 14366.
def localCycle00278 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 4, .distance 0 6, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 31 1, .gapLower 4 3, .triangle 13 2, .gapLower 0 2, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle b8a430748308a53667d55cf2964a0213b72dc9b531e45e3ed89503a601ab9532; original global index 14408.
def localCycle00279 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 6, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![4, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 11 2, .gapLower 6 3, .triangle 27 1, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle b9615bdb3e9cbbc0f58bad2bd39867096cc15a6bf9dca9801cbf7d5f32d19e11; original global index 14466.
def localCycle00280 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 4 2, .gapLower 6 2, .corridorLower 2 6, .thetaLower 2]

-- Original cycle b969c110aa51248aa1b4ee1f64ce4b1da3280508b2fc69e3abf1f53354cfe5d5; original global index 14468.
def localCycle00281 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 11 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle b9bd58b0ee404814b9bfcedb5114bec537d2998687262c3c7d302b2ffee17358; original global index 14497.
def localCycle00282 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 4 2, .triangle 8 1, .gapLower 6 2, .corridorLower 3 6, .thetaLower 3]

-- Original cycle b9e45442103a3d6d60591f537798779473ffcce4689b6a544c7015d99af74d7b; original global index 14515.
def localCycle00283 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 21 0, .triangle 19 0, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle b9e9f5cc39fb62169bb42c57c57d6f776afe4de6f82c2f4fcd0263a2f296db78; original global index 14516.
def localCycle00284 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 4 2, .triangle 8 1, .gapLower 6 0]

-- Original cycle ba52f3e0017545ff43b439a17350f4caa3f8132215376690edd252cb874b2435; original global index 14550.
def localCycle00285 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -3, 3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle bd810857b8c6a87cd06bb876479e0c527897b3d7dd7b78ccf80443fafd2de446; original global index 14782.
def localCycle00286 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 6, .distance 2 6, .distance 2 3, .theta 3]
    constant := ![3, -1, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .gapLower 5 3, .gapLower 0 4, .gapLower 0 3, .triangle 8 1, .triangle 27 1, .gapLower 3 0]

-- Original cycle bdf94e4d7faa836c8082e571ba73fd509986cc7c3a9fa4371e4b5f7b1a987263; original global index 14815.
def localCycle00287 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 4, .distance 0 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 31 1, .gapLower 4 3, .gapLower 0 3, .triangle 4 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle beb8927aa8df883f5d512a7a264d22d34ac3430b4fdb5bb74c00b4b6fefa5028; original global index 14879.
def localCycle00288 : Cycle where
  length := 5
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 6, .theta 0]
    constant := ![2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 7 2, .triangle 12 1, .gapLower 0 3, .corridorLower 0 6]

-- Original cycle bf1f17e8959fe2d70e2195dac05bffb8d84ccb9253def24822ed73448707cf28; original global index 14912.
def localCycle00289 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .theta 6, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -2, 2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 30 0, .gapLower 6 0, .gapLower 6 6, .triangle 32 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle c0140fe255e0a7c22844f13bcd18b1965389af21c8ab242a257ab90dfdcaa34b; original global index 14993.
def localCycle00290 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 32 2, .gapUpper 3 6, .thetaLower 3]

-- Original cycle c015a1fcf10a27ed090c352e9194726a8e5a74cc25a7a755464bfa18ba972533; original global index 14994.
def localCycle00291 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 6, .distance 0 5, .distance 2 5, .theta 2]
    constant := ![3, 0, -1, 0, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 11 2, .gapLower 0 4, .gapLower 5 1, .corridorLower 2 5]

-- Original cycle c034b4b9468f9e6183941631fbab3b59f2ec9461d0cf2bcd87b3ecd15725ff5a; original global index 15005.
def localCycle00292 : Cycle where
  length := 13
  data := {
    node := ![.theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .distance 4 6, .theta 4, .theta 3, .distance 1 3, .distance 3 5, .distance 3 4, .distance 3 6, .distance 0 3, .distance 0 1, .theta 0]
    constant := ![2, -1, 0, -1, -1, 0, 3, -1, 0, 0, -1, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, true, false, true, false] }
  origin := ![.gapLower 0 6, .triangle 7 0, .triangle 28 1, .triangle 29 0, .corridorLower 4 6, .thetaNext 3, .corridorUpper 1 3, .triangle 20 0, .triangle 31 1, .triangle 32 2, .triangle 11 0, .triangle 1 1, .gapLower 0 0]

-- Original cycle c03c06f106ab7558003249538f7c5211d73985010a6a0c7205d57237994cb2a3; original global index 15009.
def localCycle00293 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle c142bd0e8913dd075b40f2737d5ebd158fd9954a6e8f5bc55f8be58bbe01cca2; original global index 15087.
def localCycle00294 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle c1452cbddf837503800f424b77a02b3c6ad9635e4981dd4e021f69b78a1da771; original global index 15089.
def localCycle00295 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 1, .triangle 30 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle c19321dbb69666de97c4d31e4162c91599c6f61ad1f047e5cfb007f69a70737b; original global index 15119.
def localCycle00296 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 4]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 23 1]

-- Original cycle c1da5ebef3fb4dee120d6639a5cc4101780d3e52feaf70dd379a2cea827e577c; original global index 15138.
def localCycle00297 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .gapLower 6 3, .corridorLower 5 6]

-- Original cycle c2606bebbe346d46f66360e3c9ee272594c3094d1bc8485a7aa0041cffa84159; original global index 15175.
def localCycle00298 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 3, .gapUpper 5 3]

-- Original cycle c2e6aca958a3169557f548f7ee2ba836e8fa8d5040455a437eb61eadc131180a; original global index 15209.
def localCycle00299 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 1 6, .distance 1 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 23 1]

-- Original cycle c32f677b8d2514104e3024e311e78cbec874b633ad174599ed24b3aa573ea39e; original global index 15228.
def localCycle00300 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 30 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle c4a2e9278b2344b0fdd531b4f0204084217307b790de4163fa177709d4b829c1; original global index 15334.
def localCycle00301 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 3, .triangle 21 1, .triangle 20 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c6992244f03acb570b377691b991ec6300f260318560cc07f6b43d26393ea831; original global index 15490.
def localCycle00302 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 4, .distance 2 3, .distance 2 6, .distance 3 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 27 2, .gapLower 6 2, .triangle 33 1, .corridorLower 3 5, .thetaNext 2]

-- Original cycle c6bf76d9f7a65bf3fa03bb82e4c984b0b829e103cd6d9214e63dd52ee68ada55; original global index 15508.
def localCycle00303 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 3 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 21 1, .triangle 11 2, .triangle 8 1, .gapLower 6 0]

-- Original cycle c700228370a85c2cf658991dbaa09533bc9ff4bae370bf86700728c78c7d6758; original global index 15529.
def localCycle00304 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle c7bac2866cf2ea99b0ab54427599a75ace04f584df2b233b9ed3128f9b7d15ee; original global index 15593.
def localCycle00305 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 2 5, .distance 2 6, .distance 5 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 26 2, .triangle 30 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle c905d8990c233d901335e7d27ea420c35b3f9dfaa7a93498e048635dfbdc442a; original global index 15701.
def localCycle00306 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle ca4b9b660b3e9761b1052e98f0922d4abf38e7ebe38e4e89481afd4b0a2b12e1; original global index 15811.
def localCycle00307 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 32 2, .triangle 11 2, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle cc8ee7ddafbf454fb98275c3561830e69893839b2f46465d729f315112afdc52; original global index 15987.
def localCycle00308 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle cd45dbb00204e7a62ec874377c90494ddb6a997e0884c2122e9a12634fe6aa73; original global index 16045.
def localCycle00309 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, -1, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 33 2, .triangle 11 2, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle cdeb8434fb5302096b2118f1d491b923fa9d0e714e8a7b0173194e8979143521; original global index 16082.
def localCycle00310 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle ce8bc6e1b329b4b0f3b08f350775bfbdc9fd282701c4f9cee25e0d837ab92379; original global index 16131.
def localCycle00311 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle cf29a623ae84105f8f423a806278fa1d666e3062ee7b652343acfcda22f331f2; original global index 16167.
def localCycle00312 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle cf36fa1285d1e5b25b8f38e17013fdb81e635123a3805d648a808e2abae8f67c; original global index 16173.
def localCycle00313 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0, .triangle 9 0, .triangle 1 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle cf949785d8199dfd1b848bfdad163b821d18527100fae470d287a55033df235a; original global index 16195.
def localCycle00314 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 5, .distance 0 4, .distance 2 4, .theta 2]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .triangle 14 1, .gapLower 0 3, .gapLower 4 1, .corridorLower 2 4]

-- Original cycle cfa312457f1d472d65cf6fe46eedb68cfa6165ed18ac9c4d015deb1dda424491; original global index 16202.
def localCycle00315 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 3, .triangle 21 1, .triangle 19 0, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle d1f9a7ea6dc4672df44fb747e65cad456bf94d8105abcbc02e3ecc02d396dd65; original global index 16387.
def localCycle00316 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 21 0]

-- Original cycle d378848c4f66c2085cbcbd4ffb0bb0babbf8ba16f3d16b401961749df5357d19; original global index 16499.
def localCycle00317 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 32 2, .gapLower 6 3, .triangle 8 1, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle d37a169bb26ef67b3ad6d62c2ff6146533bdf1e600b5504d9c67844f0c510e90; original global index 16500.
def localCycle00318 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 2 5, .distance 2 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 26 2, .triangle 30 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle d3b5cbac57da83662f63690d5f59b3a11636a8228d47ed87ff19cefc05b458eb; original global index 16521.
def localCycle00319 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle d3f0ab1cc517680327776045ea4b90fc8785d2bf73813029bd9d4b5ae8cfb6ca; original global index 16542.
def localCycle00320 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 0 5, .distance 0 3]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 3 2, .gapLower 5 3, .gapLower 0 2]

-- Original cycle d4003c6a03d31972b032f0f8539ea45837388ad4a14458ff114d9a0b67259e47; original global index 16546.
def localCycle00321 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .gapLower 6 2, .triangle 29 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle d4ee9de74fdf2160721c207fbed163245652bf670b1a17a8e51b97f1cc4b0122; original global index 16613.
def localCycle00322 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d4fc5d191c0c27dc1bd9387b4fc8d32493e123a0dfb52a8867e1e33d142ad6ef; original global index 16618.
def localCycle00323 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 3 6, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 33 1, .triangle 31 1, .triangle 9 0, .triangle 1 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle d514ea78caa13f27df55697a6423df6e3755a2d66d3d6d97b7d4dc7dea2c439c; original global index 16628.
def localCycle00324 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 3 2, .gapLower 4 2, .gapLower 0 2]

-- Original cycle d57eb9c99e4666894da813a553e192cf137a371fb194f4e858416fa70b74fede; original global index 16666.
def localCycle00325 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 3 6, .distance 0 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 11 2, .triangle 14 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle d5b4b2de133eb86c2e7f1bc6c4944be1a06471359b08167fbcd3eed601a00296; original global index 16682.
def localCycle00326 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle d64996a2fed11130900358758a5794a45de4927b48129d02e1940218b7e61dad; original global index 16731.
def localCycle00327 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 11 2, .gapLower 0 4, .triangle 12 1, .triangle 9 1, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle d70fdb3bf4d903ccea236bc528e2b9030b0b0ef12721bb31e473008afa191f50; original global index 16786.
def localCycle00328 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle d72efba199f46a8d7737c7a16ae29a146904ba6913a21f3e3df19042a0499853; original global index 16793.
def localCycle00329 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle d7a3a45149d8671f83551657b258433995f790a7018708becdd8f952ab835f8b; original global index 16830.
def localCycle00330 : Cycle where
  length := 5
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 6, .distance 0 4, .distance 0 5, .theta 0]
    constant := ![2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 8 2, .triangle 13 1, .gapLower 0 3, .corridorLower 0 5]

-- Original cycle d81a4beba309391090422c0ba31ea936c45b3d484fd9db4614990f8b619fa203; original global index 16865.
def localCycle00331 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle d840d61db4573497ad807cae18a2666ccbca07f2856aa75b9f270eeff28b122a; original global index 16880.
def localCycle00332 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, 0, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 14 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle d8a417dd2532b26b67f7696766aed495dd8dc031f3368d94f26c88ee410dd1af; original global index 16909.
def localCycle00333 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 21 2, .triangle 4 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle d8ac257bf232308a6cdd26a90a8356b8b2508684f7bf0d482e73b73abd1ce779; original global index 16914.
def localCycle00334 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle d971d7de2cded3412e343190e6251c9af6307235e1fb97b17e4b7b7887536e49; original global index 16994.
def localCycle00335 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 20 1, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle da255d582fd9028dae19a564c459e3228c53e6b86c304b5b3f1e125d02e00947; original global index 17046.
def localCycle00336 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 4, .distance 0 5, .distance 2 5, .theta 2]
    constant := ![3, 0, -1, 0, 0, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 32 1, .gapLower 4 3, .gapLower 0 3, .gapLower 5 2, .corridorLower 2 5]

-- Original cycle da63a282cb4dc5c620cf3644ae36bf2cfa380c1398e82b865b25cda0a802223b; original global index 17065.
def localCycle00337 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 2, .distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, -1, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 8 0, .triangle 30 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle dafbb79ca2110ed29604845fb55807794cda057a4f7e0e0d64b8fe7ae9201aaf; original global index 17113.
def localCycle00338 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 6, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .triangle 12 1, .gapLower 0 3, .triangle 8 1, .triangle 27 1, .corridorLower 2 3]

-- Original cycle db5178526a206d52cdc2b35e51dd4f5e7f7c071a4b9cf25cb125f4545fe3e8b5; original global index 17146.
def localCycle00339 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 0, .gapLower 4 3, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle dbe7a26dc95ff77d94e468bfeb132de7a57024e255101a27a6124ca4406c0276; original global index 17187.
def localCycle00340 : Cycle where
  length := 4
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 6, .distance 0 5, .theta 0]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 8 2, .gapLower 0 4, .corridorLower 0 5]

-- Original cycle dd0c9b63a447098b2b737551bb1c3470c16e0a8dccfdad8d7bbea21419728c70; original global index 17280.
def localCycle00341 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 0 5, .distance 0 3]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 3 2, .gapLower 5 3, .gapLower 0 2]

-- Original cycle dd2b73e623852df88eea67546047e38e28e6e58ea005290a76fd65c972e2c2bd; original global index 17292.
def localCycle00342 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 6]
    constant := ![3, -2, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 4 2, .triangle 8 1, .triangle 29 1, .gapLower 6 0]

-- Original cycle dd51f64158848588ffcc0caf35485f69722a7b7962dcdfd07be4ca869786774d; original global index 17303.
def localCycle00343 : Cycle where
  length := 4
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 6, .distance 0 4, .theta 0]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 8 2, .gapLower 0 4, .corridorLower 0 4]

-- Original cycle dd72740fc451e487445d50b903d41790c74bb3091f1c5c5a78c22a37f0948bb6; original global index 17312.
def localCycle00344 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle de2989011c7c79e7e261bdd2aa0a70243f1f1e643af6b7f29020cfd8d2b2ad71; original global index 17371.
def localCycle00345 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 3 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 2, .gapLower 6 4, .gapLower 6 3, .triangle 8 1, .triangle 29 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle de2d1ea8ca70552e65c70efd3a189f975143e376363e6e77bbf0f6448b0b343a; original global index 17373.
def localCycle00346 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 3 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![4, 0, -1, 0, -2, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .gapLower 6 3, .triangle 14 1, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle de887bbcb918d144c803941576c0ab899080e7e84ec53666772e6d41cd53ffb9; original global index 17399.
def localCycle00347 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .gapLower 6 1, .triangle 30 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle dfa2c3f6c62c6d8c247edf7322b30170ed8050529ea4180fd751cc509b608c54; original global index 17468.
def localCycle00348 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .triangle 8 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle dfe29c603dae67e669cd9a7132d7975dddb8147e4f221d4f5f103d697199ceaa; original global index 17496.
def localCycle00349 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 23 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle e0ae0b2f76484472628d88e20f897bc3713c5a0cfc67c77cc8d120c5574b7ff8; original global index 17568.
def localCycle00350 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 23 0]

-- Original cycle e0afebd8b22e893ef418c4eb31324055d373aa4e6ddbe101af409ca1aaf72f71; original global index 17570.
def localCycle00351 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle e29a6de99de721615bed2a865fd2481a842dc771cf14b5031257789351f82491; original global index 17719.
def localCycle00352 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 4 6, .theta 6]
    constant := ![3, -2, 0, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 4 2, .triangle 8 1, .triangle 27 1, .triangle 32 1, .gapLower 6 0]

-- Original cycle e36bb1c89e2d34c4fbf787d27d0d1e49b42d1642a822f2b19db2d36a20747296; original global index 17785.
def localCycle00353 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 3 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .triangle 11 2, .triangle 8 1, .gapLower 6 0]

-- Original cycle e5bbef6b8142383e6ae07e926a32a591b44093bd1828dfd1b26ca44dfd8e3659; original global index 17972.
def localCycle00354 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle e683807d92401ca2094318443c8f1576ec984832c57838826903ed877b8568ad; original global index 18032.
def localCycle00355 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 6, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .gapLower 6 2, .gapLower 6 1, .triangle 27 1, .corridorLower 2 3]

-- Original cycle e7a45e9db75cee71f81f4eb704a0aae7c2382b9388832270eeba1b9155716cb0; original global index 18117.
def localCycle00356 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 3 2, .gapLower 4 2, .gapLower 0 2]

-- Original cycle e8e0bd27bbffb1e65c366c577e9175abb312ad012ce013857af5658b86d98955; original global index 18202.
def localCycle00357 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 6 4, .triangle 8 1, .gapLower 6 2, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle e912bf83f04c461a0044fab162a2642f4ad844223f0642cff36f0db158dcd7bc; original global index 18216.
def localCycle00358 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle e9de01624fac3b3bbdff4808c35f89a962379955d6db26678c390116d42e5f6b; original global index 18273.
def localCycle00359 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 5 6]

-- Original cycle ebc9c7115eded2a1058dba0a4e5dda62b9b5eeeb245aaf4369753be0ad4ecb8f; original global index 18397.
def localCycle00360 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 2 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -2, 0, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .gapLower 5 2, .triangle 28 1, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle ebdde38f980d2140086757a7c3ee801adcf16624463b7669379b908574bee0e1; original global index 18407.
def localCycle00361 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 3 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 21 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle ec369d3bf84759445dc146ea91440c3b3c9671c27e45c0076ff619f185a2d923; original global index 18437.
def localCycle00362 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 21 1, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ecf6ddb9936bc7d7d7078b04e87c6983a221aeb60d667fc9ea9b1a472a8c22e9; original global index 18497.
def localCycle00363 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 14 2, .gapLower 6 2, .gapUpper 5 2]

-- Original cycle ed322721869d6195fa86a0ea80b498d5adf7218af9464fc0088adf31d47e18c1; original global index 18519.
def localCycle00364 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -3, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 6 4, .triangle 8 1, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle ed55cadd9cc84b65e217c8ddf2331015bfc42775c1e81b027a509630ca3e9940; original global index 18527.
def localCycle00365 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 32 2, .gapLower 6 3, .triangle 21 1, .triangle 20 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ed8021a415beaa7a2046c0be8bcbbe24ca31dcc8836b4ac5884c823ae5f778a5; original global index 18540.
def localCycle00366 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![4, 0, -1, -1, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 20 0, .triangle 21 0, .gapLower 6 3, .triangle 8 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle edd4a03bd1c555dc0330951aed18706c6e399c633f6da248c56959814c5547f5; original global index 18569.
def localCycle00367 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 31 1, .gapLower 4 2, .gapLower 0 2, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle ee64d74f3567e826849823f40e37d59db28578c35529517629ff5e10ce4d5fc0; original global index 18610.
def localCycle00368 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 4]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 5, .gapLower 6 4, .gapLower 6 3, .triangle 23 1]

-- Original cycle ee9cfed25cd31422b638e569729dfaeb81d4df1c220328d54dc56b7dcfe621f1; original global index 18621.
def localCycle00369 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 28 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle eea9304f7761f67e042b7bbfef901da15ac889932a82a743fe1b489697986c9c; original global index 18625.
def localCycle00370 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 2 4, .theta 2]
    constant := ![3, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .gapLower 0 4, .gapLower 4 2, .corridorLower 2 4]

-- Original cycle ef9521357f9d73a0f2c021f599ce516d4324d8ee280b998f331c09f17592dec2; original global index 18692.
def localCycle00371 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .gapLower 0 3, .corridorLower 0 4, .thetaLower 0]

-- Original cycle f0740b4f2161a6bd3563c89b85f4f93cd1a2426c832fa78b67ff160ebbe6a803; original global index 18750.
def localCycle00372 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, 0, -1, -1, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .gapLower 6 3, .triangle 14 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle f0a9824bda98e96d1af51cdb4ae5de3999ca7bcd40212e871e3f122c19ce08e6; original global index 18770.
def localCycle00373 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .corridorLower 5 6]

-- Original cycle f0acb9e89236adf1e7779236485b6868cd39227665ca51ab8b440fbcd1260363; original global index 18773.
def localCycle00374 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 5, .distance 1 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .triangle 11 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle f0d43741bd9d43922c1628767eadd1f17ae8af4d18bb08a1097e27b872d86bdc; original global index 18784.
def localCycle00375 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -2, 2, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .gapLower 6 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3]

-- Original cycle f3227770fe028ee1dbb5364ac375d6e77abf119833b11d3e0fff8e33469cd7f5; original global index 18955.
def localCycle00376 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 3 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 11 2, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle f3829b7f72b2380ca3c0cf9713c573eb64c9337cbe7715f67e825039c066cee5; original global index 18997.
def localCycle00377 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 9 2, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle f57e2a7d1ef90b341a6a0622c0980b6068a7c4a6f5abf164b5eb979617eafd74; original global index 19141.
def localCycle00378 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle f5b5c401aecd0240a7e38dc5a366bfa8d4bc8939c6a9b866c7ae5f4e211f4d77; original global index 19164.
def localCycle00379 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 32 2, .gapLower 6 3, .triangle 8 1, .triangle 29 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle f65a2bbe18b13c626b9d9c5697b8683d7cdc3ce1196779d38da49f3ee4d6b244; original global index 19214.
def localCycle00380 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle f70225bdb672e6781ec0f73c51cbecd6d7afe68189da96b7f862bc64396f9f53; original global index 19265.
def localCycle00381 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 0, .triangle 28 0, .triangle 29 0, .corridorLower 4 6, .thetaNext 3]

-- Original cycle f7e06c3feb0e42a7d9d79de4a2c1324322932837bb6100a99019eb77a35b3df3; original global index 19324.
def localCycle00382 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 4, .distance 0 5, .distance 2 5, .theta 2]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .triangle 13 1, .gapLower 0 3, .gapLower 5 2, .corridorLower 2 5]

-- Original cycle f7ee3090f76922de3445a6ec0317de81b062f998a33469e0de27a798a88829fd; original global index 19328.
def localCycle00383 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 1, .corridorLower 2 6, .thetaLower 2]

-- Original cycle f83922ea4fb74b556e40e2b07165d202a562524ae4897636d68fe9d1ac1d4aee; original global index 19360.
def localCycle00384 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 2, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle fa38705ef9a7c53d1b22a8aa05fc90a3609ab60db46e0d3e9c922bd2cc8c028e; original global index 19512.
def localCycle00385 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 3 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 2, .gapLower 6 4, .triangle 11 2, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle fa475957f588ba08ea0a6368b1d1853f1fd1fca52f0f2808d5e72fb0f578d9a3; original global index 19521.
def localCycle00386 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 5]
    constant := ![2, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 32 2, .gapLower 6 3, .triangle 24 1]

-- Original cycle fc13bfc353811fb20032440ce9ee8a3f45b2e28a193a8ecd06893890e5b300ea; original global index 19682.
def localCycle00387 : Cycle where
  length := 4
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .theta 5, .zero]
    constant := ![0, 1, -2, 0]
    coefficient := ![1, 1, -1, 0]
    strict := ![false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapUpper 5 6, .thetaLower 5]

-- Original cycle fc2002a8e79135f2cf3bbe1b8095adc484bb97f3843ccc473b6f10d0ae266589; original global index 19687.
def localCycle00388 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle fc2c0d85d9b891a35dc2dbd77fcdac2378817cfcf7831b161a81026c70dfa873; original global index 19692.
def localCycle00389 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle fc9b8e09b1329a174944d6d1cec6b563779e26434f0c3dc3144dbc37b41823e7; original global index 19733.
def localCycle00390 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 5, .distance 2 5, .distance 2 4, .distance 4 6, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .gapLower 5 2, .triangle 28 1, .triangle 29 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle fdcf005a25cef2ea17bf9c5fab06c510094a07a3195e1f30bbdf1e1954269a6e; original global index 19836.
def localCycle00391 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle fe0d15375d56cf16cf430f2fe7e37592088d2989d18c195d766101f3ef598d15; original global index 19853.
def localCycle00392 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 3 2, .triangle 14 2, .gapLower 6 2, .triangle 30 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle fe37fb6f3c50e5058105329eaf1efde927fe99649238014b919cd244ceb742e4; original global index 19870.
def localCycle00393 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 6, .distance 2 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 2, .triangle 14 2, .gapLower 6 2, .triangle 29 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle fe4f9ac9a03645fd64eb2a47b232d203971e9fa053171822bf40b97769576290; original global index 19880.
def localCycle00394 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .zero]
    constant := ![0, 2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 4 2, .triangle 14 1, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .thetaLower 2]

-- Original cycle fee853d55a05f4d5e3148bc5d8626ef79d0a86ea52e353cef350b67c04807772; original global index 19931.
def localCycle00395 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 24 2, .triangle 4 2, .gapLower 6 2, .triangle 29 1, .gapLower 6 0]

-- Original cycle ff78164d894f3f2dd9e1cfd4d9b2fd42dab53d8ea2d2e40f0e79a6aa9348f1a0; original global index 19974.
def localCycle00396 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle ffed92dad58b532cf0260eb4741342ffbc93ccb3e99f08b7819ee86aef47638f; original global index 20018.
def localCycle00397 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 4, .zero]
    constant := ![0, 3, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 4 2, .triangle 8 1, .gapLower 6 1, .corridorLower 4 6, .thetaLower 4]

def library : Library := fun id => if id < 199 then (if id < 99 then (if id < 49 then (if id < 24 then (if id < 12 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))))) else (if id < 18 then (if id < 15 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))) else (if id < 21 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))))) else (if id < 36 then (if id < 30 then (if id < 27 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none))) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)))) else (if id < 33 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none))))) else (if id < 42 then (if id < 39 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none)))) else (if id < 45 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))) else (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none))))))) else (if id < 74 then (if id < 61 then (if id < 55 then (if id < 52 then (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)))) else (if id < 58 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none))) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))))) else (if id < 67 then (if id < 64 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)))) else (if id < 70 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none))) else (if id < 72 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)))))) else (if id < 86 then (if id < 80 then (if id < 77 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none))) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)))) else (if id < 83 then (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none))) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none))))) else (if id < 92 then (if id < 89 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none))) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)))) else (if id < 95 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none))) else (if id < 97 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)))))))) else (if id < 149 then (if id < 124 then (if id < 111 then (if id < 105 then (if id < 102 then (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none))) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)))) else (if id < 108 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none))) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none))))) else (if id < 117 then (if id < 114 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none))) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)))) else (if id < 120 then (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none))) else (if id < 122 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)))))) else (if id < 136 then (if id < 130 then (if id < 127 then (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none))) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none)))) else (if id < 133 then (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none))) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none))))) else (if id < 142 then (if id < 139 then (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none))) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none)))) else (if id < 145 then (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none))) else (if id < 147 then (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none)) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none))))))) else (if id < 174 then (if id < 161 then (if id < 155 then (if id < 152 then (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none))) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none)))) else (if id < 158 then (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none))) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none))))) else (if id < 167 then (if id < 164 then (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none))) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none)))) else (if id < 170 then (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none))) else (if id < 172 then (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id = 171 then some localCycle00171 else none)) else (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id = 173 then some localCycle00173 else none)))))) else (if id < 186 then (if id < 180 then (if id < 177 then (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none))) else (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none)))) else (if id < 183 then (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none))) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id = 185 then some localCycle00185 else none))))) else (if id < 192 then (if id < 189 then (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none))) else (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id = 191 then some localCycle00191 else none)))) else (if id < 195 then (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none))) else (if id < 197 then (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none)) else (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id = 198 then some localCycle00198 else none))))))))) else (if id < 298 then (if id < 248 then (if id < 223 then (if id < 211 then (if id < 205 then (if id < 202 then (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none))) else (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id = 204 then some localCycle00204 else none)))) else (if id < 208 then (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none))) else (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id = 210 then some localCycle00210 else none))))) else (if id < 217 then (if id < 214 then (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id = 213 then some localCycle00213 else none))) else (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id < 216 then (if id = 215 then some localCycle00215 else none) else (if id = 216 then some localCycle00216 else none)))) else (if id < 220 then (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id = 219 then some localCycle00219 else none))) else (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id = 222 then some localCycle00222 else none)))))) else (if id < 235 then (if id < 229 then (if id < 226 then (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id = 225 then some localCycle00225 else none))) else (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id < 228 then (if id = 227 then some localCycle00227 else none) else (if id = 228 then some localCycle00228 else none)))) else (if id < 232 then (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id < 231 then (if id = 230 then some localCycle00230 else none) else (if id = 231 then some localCycle00231 else none))) else (if id < 233 then (if id = 232 then some localCycle00232 else none) else (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id = 234 then some localCycle00234 else none))))) else (if id < 241 then (if id < 238 then (if id < 236 then (if id = 235 then some localCycle00235 else none) else (if id < 237 then (if id = 236 then some localCycle00236 else none) else (if id = 237 then some localCycle00237 else none))) else (if id < 239 then (if id = 238 then some localCycle00238 else none) else (if id < 240 then (if id = 239 then some localCycle00239 else none) else (if id = 240 then some localCycle00240 else none)))) else (if id < 244 then (if id < 242 then (if id = 241 then some localCycle00241 else none) else (if id < 243 then (if id = 242 then some localCycle00242 else none) else (if id = 243 then some localCycle00243 else none))) else (if id < 246 then (if id < 245 then (if id = 244 then some localCycle00244 else none) else (if id = 245 then some localCycle00245 else none)) else (if id < 247 then (if id = 246 then some localCycle00246 else none) else (if id = 247 then some localCycle00247 else none))))))) else (if id < 273 then (if id < 260 then (if id < 254 then (if id < 251 then (if id < 249 then (if id = 248 then some localCycle00248 else none) else (if id < 250 then (if id = 249 then some localCycle00249 else none) else (if id = 250 then some localCycle00250 else none))) else (if id < 252 then (if id = 251 then some localCycle00251 else none) else (if id < 253 then (if id = 252 then some localCycle00252 else none) else (if id = 253 then some localCycle00253 else none)))) else (if id < 257 then (if id < 255 then (if id = 254 then some localCycle00254 else none) else (if id < 256 then (if id = 255 then some localCycle00255 else none) else (if id = 256 then some localCycle00256 else none))) else (if id < 258 then (if id = 257 then some localCycle00257 else none) else (if id < 259 then (if id = 258 then some localCycle00258 else none) else (if id = 259 then some localCycle00259 else none))))) else (if id < 266 then (if id < 263 then (if id < 261 then (if id = 260 then some localCycle00260 else none) else (if id < 262 then (if id = 261 then some localCycle00261 else none) else (if id = 262 then some localCycle00262 else none))) else (if id < 264 then (if id = 263 then some localCycle00263 else none) else (if id < 265 then (if id = 264 then some localCycle00264 else none) else (if id = 265 then some localCycle00265 else none)))) else (if id < 269 then (if id < 267 then (if id = 266 then some localCycle00266 else none) else (if id < 268 then (if id = 267 then some localCycle00267 else none) else (if id = 268 then some localCycle00268 else none))) else (if id < 271 then (if id < 270 then (if id = 269 then some localCycle00269 else none) else (if id = 270 then some localCycle00270 else none)) else (if id < 272 then (if id = 271 then some localCycle00271 else none) else (if id = 272 then some localCycle00272 else none)))))) else (if id < 285 then (if id < 279 then (if id < 276 then (if id < 274 then (if id = 273 then some localCycle00273 else none) else (if id < 275 then (if id = 274 then some localCycle00274 else none) else (if id = 275 then some localCycle00275 else none))) else (if id < 277 then (if id = 276 then some localCycle00276 else none) else (if id < 278 then (if id = 277 then some localCycle00277 else none) else (if id = 278 then some localCycle00278 else none)))) else (if id < 282 then (if id < 280 then (if id = 279 then some localCycle00279 else none) else (if id < 281 then (if id = 280 then some localCycle00280 else none) else (if id = 281 then some localCycle00281 else none))) else (if id < 283 then (if id = 282 then some localCycle00282 else none) else (if id < 284 then (if id = 283 then some localCycle00283 else none) else (if id = 284 then some localCycle00284 else none))))) else (if id < 291 then (if id < 288 then (if id < 286 then (if id = 285 then some localCycle00285 else none) else (if id < 287 then (if id = 286 then some localCycle00286 else none) else (if id = 287 then some localCycle00287 else none))) else (if id < 289 then (if id = 288 then some localCycle00288 else none) else (if id < 290 then (if id = 289 then some localCycle00289 else none) else (if id = 290 then some localCycle00290 else none)))) else (if id < 294 then (if id < 292 then (if id = 291 then some localCycle00291 else none) else (if id < 293 then (if id = 292 then some localCycle00292 else none) else (if id = 293 then some localCycle00293 else none))) else (if id < 296 then (if id < 295 then (if id = 294 then some localCycle00294 else none) else (if id = 295 then some localCycle00295 else none)) else (if id < 297 then (if id = 296 then some localCycle00296 else none) else (if id = 297 then some localCycle00297 else none)))))))) else (if id < 348 then (if id < 323 then (if id < 310 then (if id < 304 then (if id < 301 then (if id < 299 then (if id = 298 then some localCycle00298 else none) else (if id < 300 then (if id = 299 then some localCycle00299 else none) else (if id = 300 then some localCycle00300 else none))) else (if id < 302 then (if id = 301 then some localCycle00301 else none) else (if id < 303 then (if id = 302 then some localCycle00302 else none) else (if id = 303 then some localCycle00303 else none)))) else (if id < 307 then (if id < 305 then (if id = 304 then some localCycle00304 else none) else (if id < 306 then (if id = 305 then some localCycle00305 else none) else (if id = 306 then some localCycle00306 else none))) else (if id < 308 then (if id = 307 then some localCycle00307 else none) else (if id < 309 then (if id = 308 then some localCycle00308 else none) else (if id = 309 then some localCycle00309 else none))))) else (if id < 316 then (if id < 313 then (if id < 311 then (if id = 310 then some localCycle00310 else none) else (if id < 312 then (if id = 311 then some localCycle00311 else none) else (if id = 312 then some localCycle00312 else none))) else (if id < 314 then (if id = 313 then some localCycle00313 else none) else (if id < 315 then (if id = 314 then some localCycle00314 else none) else (if id = 315 then some localCycle00315 else none)))) else (if id < 319 then (if id < 317 then (if id = 316 then some localCycle00316 else none) else (if id < 318 then (if id = 317 then some localCycle00317 else none) else (if id = 318 then some localCycle00318 else none))) else (if id < 321 then (if id < 320 then (if id = 319 then some localCycle00319 else none) else (if id = 320 then some localCycle00320 else none)) else (if id < 322 then (if id = 321 then some localCycle00321 else none) else (if id = 322 then some localCycle00322 else none)))))) else (if id < 335 then (if id < 329 then (if id < 326 then (if id < 324 then (if id = 323 then some localCycle00323 else none) else (if id < 325 then (if id = 324 then some localCycle00324 else none) else (if id = 325 then some localCycle00325 else none))) else (if id < 327 then (if id = 326 then some localCycle00326 else none) else (if id < 328 then (if id = 327 then some localCycle00327 else none) else (if id = 328 then some localCycle00328 else none)))) else (if id < 332 then (if id < 330 then (if id = 329 then some localCycle00329 else none) else (if id < 331 then (if id = 330 then some localCycle00330 else none) else (if id = 331 then some localCycle00331 else none))) else (if id < 333 then (if id = 332 then some localCycle00332 else none) else (if id < 334 then (if id = 333 then some localCycle00333 else none) else (if id = 334 then some localCycle00334 else none))))) else (if id < 341 then (if id < 338 then (if id < 336 then (if id = 335 then some localCycle00335 else none) else (if id < 337 then (if id = 336 then some localCycle00336 else none) else (if id = 337 then some localCycle00337 else none))) else (if id < 339 then (if id = 338 then some localCycle00338 else none) else (if id < 340 then (if id = 339 then some localCycle00339 else none) else (if id = 340 then some localCycle00340 else none)))) else (if id < 344 then (if id < 342 then (if id = 341 then some localCycle00341 else none) else (if id < 343 then (if id = 342 then some localCycle00342 else none) else (if id = 343 then some localCycle00343 else none))) else (if id < 346 then (if id < 345 then (if id = 344 then some localCycle00344 else none) else (if id = 345 then some localCycle00345 else none)) else (if id < 347 then (if id = 346 then some localCycle00346 else none) else (if id = 347 then some localCycle00347 else none))))))) else (if id < 373 then (if id < 360 then (if id < 354 then (if id < 351 then (if id < 349 then (if id = 348 then some localCycle00348 else none) else (if id < 350 then (if id = 349 then some localCycle00349 else none) else (if id = 350 then some localCycle00350 else none))) else (if id < 352 then (if id = 351 then some localCycle00351 else none) else (if id < 353 then (if id = 352 then some localCycle00352 else none) else (if id = 353 then some localCycle00353 else none)))) else (if id < 357 then (if id < 355 then (if id = 354 then some localCycle00354 else none) else (if id < 356 then (if id = 355 then some localCycle00355 else none) else (if id = 356 then some localCycle00356 else none))) else (if id < 358 then (if id = 357 then some localCycle00357 else none) else (if id < 359 then (if id = 358 then some localCycle00358 else none) else (if id = 359 then some localCycle00359 else none))))) else (if id < 366 then (if id < 363 then (if id < 361 then (if id = 360 then some localCycle00360 else none) else (if id < 362 then (if id = 361 then some localCycle00361 else none) else (if id = 362 then some localCycle00362 else none))) else (if id < 364 then (if id = 363 then some localCycle00363 else none) else (if id < 365 then (if id = 364 then some localCycle00364 else none) else (if id = 365 then some localCycle00365 else none)))) else (if id < 369 then (if id < 367 then (if id = 366 then some localCycle00366 else none) else (if id < 368 then (if id = 367 then some localCycle00367 else none) else (if id = 368 then some localCycle00368 else none))) else (if id < 371 then (if id < 370 then (if id = 369 then some localCycle00369 else none) else (if id = 370 then some localCycle00370 else none)) else (if id < 372 then (if id = 371 then some localCycle00371 else none) else (if id = 372 then some localCycle00372 else none)))))) else (if id < 385 then (if id < 379 then (if id < 376 then (if id < 374 then (if id = 373 then some localCycle00373 else none) else (if id < 375 then (if id = 374 then some localCycle00374 else none) else (if id = 375 then some localCycle00375 else none))) else (if id < 377 then (if id = 376 then some localCycle00376 else none) else (if id < 378 then (if id = 377 then some localCycle00377 else none) else (if id = 378 then some localCycle00378 else none)))) else (if id < 382 then (if id < 380 then (if id = 379 then some localCycle00379 else none) else (if id < 381 then (if id = 380 then some localCycle00380 else none) else (if id = 381 then some localCycle00381 else none))) else (if id < 383 then (if id = 382 then some localCycle00382 else none) else (if id < 384 then (if id = 383 then some localCycle00383 else none) else (if id = 384 then some localCycle00384 else none))))) else (if id < 391 then (if id < 388 then (if id < 386 then (if id = 385 then some localCycle00385 else none) else (if id < 387 then (if id = 386 then some localCycle00386 else none) else (if id = 387 then some localCycle00387 else none))) else (if id < 389 then (if id = 388 then some localCycle00388 else none) else (if id < 390 then (if id = 389 then some localCycle00389 else none) else (if id = 390 then some localCycle00390 else none)))) else (if id < 394 then (if id < 392 then (if id = 391 then some localCycle00391 else none) else (if id < 393 then (if id = 392 then some localCycle00392 else none) else (if id = 393 then some localCycle00393 else none))) else (if id < 396 then (if id < 395 then (if id = 394 then some localCycle00394 else none) else (if id = 395 then some localCycle00395 else none)) else (if id < 397 then (if id = 396 then some localCycle00396 else none) else (if id = 397 then some localCycle00397 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 6, 0, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 3, 2, 0, 6, 1], ![4, 2, 3, 0, 5, 1]], proof := .tail 15 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6272)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 6, 0, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 3, 2, 6, 0, 1], ![4, 2, 3, 5, 0, 1]], proof := .tail 358 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6273)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 5, 6, 3, 4, 2], ![5, 6, 3, 4, 0, 1], ![5, 6, 2, 0, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 5]], proof := .low6 (![97, 308, 302, 260, 364, 216, 387, 245, 67, 89, 82, 352, 293, 127, 279, 92, 304, 304, 103, 357, 282, 241, 159, 64, 19, 47, 154, 388]) }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6274)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![5, 6, 3, 4, 0, 1], ![5, 6, 2, 0, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 5, 1]], proof := .tail 258 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6275)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![5, 6, 3, 4, 0, 1], ![5, 6, 2, 0, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 3, 2, 6, 0, 1], ![4, 3, 2, 5, 0, 1]], proof := .tail 230 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6276)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![6, 5, 3, 4, 0, 1], ![5, 6, 2, 0, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 3, 6, 2, 0, 1], ![4, 3, 5, 2, 0, 1]], proof := .tail 265 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6277)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![6, 5, 3, 4, 0, 1], ![6, 5, 2, 0, 1, 4], ![5, 6, 2, 0, 1, 3], ![4, 6, 3, 2, 0, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 121 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6278)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 2], ![6, 5, 3, 4, 0, 1], ![6, 5, 2, 0, 1, 4], ![6, 5, 2, 0, 1, 3], ![6, 4, 3, 2, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 277 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6279)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 4, 3, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 1, 5, 6], ![2, 0, 3, 1, 5, 6], ![2, 0, 1, 3, 4, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 344 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6280)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 4, 3, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 1, 5, 6], ![2, 0, 3, 1, 6, 5], ![2, 0, 1, 3, 6, 4], ![2, 0, 1, 3, 5, 4]], proof := .tail 102 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6281)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 4, 3, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 1, 6, 5], ![2, 0, 3, 1, 6, 5], ![2, 0, 1, 6, 3, 4], ![2, 0, 1, 5, 3, 4]], proof := .tail 335 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6282)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 4, 3, 6, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 1, 6, 5], ![2, 0, 3, 1, 6, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 1, 3, 4]], proof := .low6 (![136, 10, 137, 298, 160, 316, 57, 135, 61, 165, 348, 174, 235, 229, 18, 383, 174, 124, 145, 119, 174, 31, 35, 174, 200, 296, 45, 174]) }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6283)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 4, 3, 6, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 1, 6, 5], ![2, 0, 3, 1, 6, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 1, 3, 4]], proof := .low6 (![146, 129, 363, 91, 160, 316, 57, 106, 392, 43, 58, 174, 139, 11, 273, 273, 174, 273, 276, 306, 174, 3, 332, 174, 268, 296, 45, 174]) }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6284)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 4, 3, 6, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 4, 1, 6, 5], ![2, 0, 3, 1, 6, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .low6 (![114, 270, 393, 16, 160, 316, 57, 257, 93, 218, 147, 174, 153, 333, 152, 236, 174, 84, 321, 312, 174, 124, 373, 174, 124, 296, 45, 174]) }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6285)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 4, 6, 3, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 6, 1, 5], ![2, 0, 3, 1, 6, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 3, 1, 4]], proof := .low6 (![144, 10, 137, 297, 175, 299, 220, 396, 269, 328, 39, 328, 328, 76, 38, 272, 172, 2, 38, 56, 34, 34, 359, 155, 155, 111, 272, 362]) }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6286)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 6, 1, 5], ![2, 0, 3, 6, 1, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 3, 4, 1]], proof := .tail 176 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6287)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 4, 1, 5], ![2, 0, 6, 3, 1, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 4, 3, 1]], proof := .tail 169 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6288)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 4, 6, 3, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 6, 1, 5], ![2, 0, 3, 1, 6, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 3, 1, 4]], proof := .low6 (![144, 129, 41, 5, 248, 299, 224, 126, 328, 328, 39, 328, 328, 11, 259, 273, 273, 273, 65, 168, 113, 389, 346, 372, 372, 190, 325, 394]) }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6289)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 6, 1, 5], ![2, 0, 3, 6, 1, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 3, 4, 1]], proof := .tail 176 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6290)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 4, 1, 5], ![2, 0, 6, 3, 1, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 4, 3, 1]], proof := .tail 30 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6291)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 4, 1, 5], ![2, 6, 0, 3, 1, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 4, 0, 3, 1]], proof := .tail 195 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6292)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 4, 6, 3, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 4, 6, 1, 5], ![2, 0, 3, 1, 6, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 3, 1, 4]], proof := .low6 (![196, 37, 122, 231, 175, 299, 14, 254, 79, 391, 281, 189, 189, 118, 366, 101, 86, 86, 148, 376, 354, 384, 180, 62, 62, 111, 272, 362]) }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6293)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 4, 6, 1, 5], ![2, 0, 3, 6, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 3, 4, 1]], proof := .tail 176 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6294)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 4, 1, 5], ![2, 0, 6, 3, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 4, 3, 1]], proof := .tail 222 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6295)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 4, 1, 5], ![2, 6, 0, 3, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 4, 0, 3, 1]], proof := .tail 195 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6296)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 6, 4, 5, 0, 1], ![2, 0, 6, 4, 1, 5], ![6, 2, 0, 3, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 4, 2, 0, 3, 1]], proof := .tail 132 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6297)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 0, 4, 1, 5], ![2, 6, 0, 3, 1, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 4, 3, 0, 1]], proof := .tail 380 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6298)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 0, 4, 1, 5], ![2, 6, 0, 3, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 4, 3, 0, 1]], proof := .tail 13 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6299)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 0, 4, 1, 5], ![6, 2, 0, 3, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 4, 2, 3, 0, 1]], proof := .tail 199 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6300)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 4, 3, 5, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 0, 4, 1, 5], ![6, 2, 0, 3, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 115 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6301)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 4, 5, 3, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 5, 1, 6], ![2, 0, 3, 1, 5, 6], ![2, 0, 3, 1, 4, 6], ![2, 0, 1, 3, 4, 5]], proof := .low6 (![256, 10, 51, 163, 221, 81, 351, 100, 219, 284, 55, 253, 375, 347, 225, 228, 238, 215, 173, 228, 349, 215, 130, 365, 301, 311, 211, 290]) }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6302)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 4, 5, 3, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 5, 1, 6], ![2, 0, 3, 1, 6, 5], ![2, 0, 3, 1, 6, 4], ![2, 0, 1, 3, 5, 4]], proof := .tail 208 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6303)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 5, 4, 3, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 5, 1, 6], ![2, 0, 3, 5, 1, 6], ![2, 0, 3, 4, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 313 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6304)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 5, 4, 3, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 4, 1, 6], ![2, 0, 5, 3, 1, 6], ![2, 0, 4, 3, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 96 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6305)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 5, 4, 3, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 4, 1, 6], ![2, 5, 0, 3, 1, 6], ![2, 4, 0, 3, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 156 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6306)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 5, 4, 3, 6, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 5, 4, 1, 6], ![5, 2, 0, 3, 1, 6], ![4, 2, 0, 3, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .low6 (![285, 10, 133, 163, 63, 350, 283, 100, 219, 284, 182, 202, 212, 234, 225, 182, 202, 75, 173, 182, 202, 140, 368, 386, 315, 203, 182, 202]) }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6307)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 4, 5, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 1, 5, 6], ![2, 0, 3, 1, 4, 6], ![2, 0, 3, 1, 4, 5]], proof := .low6 (![170, 10, 44, 94, 104, 81, 177, 275, 271, 353, 303, 178, 210, 355, 116, 295, 32, 69, 109, 361, 213, 244, 323, 237, 205, 68, 192, 131]) }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6308)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 4, 5, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 1, 6, 5], ![2, 0, 3, 1, 6, 4], ![2, 0, 3, 1, 5, 4]], proof := .low0 (![167, 266, 356, 227, 291, 52, 337, 83, 367, 49, 327, 255, 255, 217, 83, 83, 83, 83, 85, 324, 324, 324, 50, 314, 371, 164, 340, 143]) }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6309)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 1, 6, 5], ![2, 0, 3, 6, 1, 4], ![2, 0, 3, 5, 1, 4]], proof := .tail 78 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6310)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 1, 6, 5], ![2, 0, 6, 3, 1, 4], ![2, 0, 5, 3, 1, 4]], proof := .tail 181 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6311)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 1, 6, 5], ![2, 6, 0, 3, 1, 4], ![2, 5, 0, 3, 1, 4]], proof := .tail 25 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6312)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 1, 6, 5], ![6, 2, 0, 3, 1, 4], ![5, 2, 0, 3, 1, 4]], proof := .low6 (![114, 270, 309, 274, 249, 299, 80, 305, 9, 107, 374, 66, 289, 88, 42, 77, 70, 318, 138, 134, 354, 108, 201, 117, 263, 111, 252, 362]) }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6313)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 6, 1, 5], ![2, 0, 3, 6, 1, 4], ![2, 0, 3, 5, 4, 1]], proof := .tail 329 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6314)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 6, 1, 5], ![2, 0, 6, 3, 1, 4], ![2, 0, 5, 3, 4, 1]], proof := .tail 329 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6315)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 6, 1, 5], ![2, 6, 0, 3, 1, 4], ![2, 5, 0, 3, 4, 1]], proof := .tail 264 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6316)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 6, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 2, 0, 3, 4, 1]], proof := .tail 300 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6317)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 4, 5, 1], ![2, 0, 6, 3, 1, 5], ![2, 0, 6, 3, 1, 4], ![2, 0, 5, 4, 3, 1]], proof := .tail 206 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6318)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 4, 5, 1], ![2, 0, 6, 3, 1, 5], ![2, 6, 0, 3, 1, 4], ![2, 5, 0, 4, 3, 1]], proof := .tail 33 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6319)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 4, 5, 1], ![2, 0, 6, 3, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 2, 0, 4, 3, 1]], proof := .tail 128 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6320)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 4, 5, 1], ![2, 6, 0, 3, 1, 5], ![2, 6, 0, 3, 1, 4], ![2, 5, 4, 0, 3, 1]], proof := .tail 149 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6321)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 4, 5, 1], ![2, 6, 0, 3, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 2, 4, 0, 3, 1]], proof := .tail 149 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6322)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 6, 4, 5, 0, 1], ![2, 0, 6, 4, 5, 1], ![6, 2, 0, 3, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 4, 2, 0, 3, 1]], proof := .low0 (![223, 7, 21, 161, 242, 151, 179, 6, 278, 287, 17, 360, 292, 90, 6, 6, 6, 6, 8, 207, 187, 123, 286, 338, 288, 370, 17, 390]) }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6323)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 5, 4, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 5, 1, 6], ![2, 0, 3, 4, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 313 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6324)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 5, 6, 1], ![2, 0, 3, 4, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 142 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6325)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 5, 6, 1], ![2, 0, 3, 4, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 209 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6326)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 6, 5, 1], ![2, 0, 3, 6, 4, 1], ![2, 0, 3, 5, 4, 1]], proof := .tail 158 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6327)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 6, 5, 1], ![2, 0, 6, 3, 4, 1], ![2, 0, 5, 3, 4, 1]], proof := .tail 186 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6328)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 6, 5, 1], ![2, 6, 0, 3, 4, 1], ![2, 5, 0, 3, 4, 1]], proof := .tail 186 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6329)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 6, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 2, 0, 3, 4, 1]], proof := .tail 186 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6330)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 4, 5, 1], ![2, 0, 6, 3, 5, 1], ![2, 0, 6, 3, 4, 1], ![2, 0, 5, 4, 3, 1]], proof := .tail 251 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6331)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 4, 5, 1], ![2, 0, 6, 3, 5, 1], ![2, 6, 0, 3, 4, 1], ![2, 5, 0, 4, 3, 1]], proof := .tail 28 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6332)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 4, 5, 1], ![2, 0, 6, 3, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 2, 0, 4, 3, 1]], proof := .tail 267 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6333)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 4, 5, 1], ![2, 6, 0, 3, 5, 1], ![2, 6, 0, 3, 4, 1], ![2, 5, 4, 0, 3, 1]], proof := .tail 71 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6334)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 4, 5, 1], ![2, 6, 0, 3, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 2, 4, 0, 3, 1]], proof := .tail 71 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6335)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 4, 5, 0, 1], ![2, 0, 6, 4, 5, 1], ![6, 2, 0, 3, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 4, 2, 0, 3, 1]], proof := .tail 322 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6336)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 5, 4, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 4, 6, 1], ![2, 0, 5, 3, 1, 6], ![2, 0, 4, 3, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 319 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6337)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 4, 6, 1], ![2, 0, 5, 3, 6, 1], ![2, 0, 4, 3, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 48 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6338)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 4, 6, 1], ![2, 0, 5, 3, 6, 1], ![2, 0, 4, 3, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 27 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6339)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 6, 4, 1], ![2, 0, 5, 6, 3, 1], ![2, 0, 4, 3, 1, 6], ![2, 0, 4, 3, 1, 5]], proof := .tail 22 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6340)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 6, 4, 1], ![2, 0, 5, 6, 3, 1], ![2, 0, 4, 3, 6, 1], ![2, 0, 4, 3, 5, 1]], proof := .tail 246 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6341)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 5, 4, 1], ![2, 0, 5, 6, 3, 1], ![2, 0, 4, 6, 3, 1], ![2, 0, 4, 5, 3, 1]], proof := .tail 20 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6342)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 5, 4, 1], ![2, 0, 6, 5, 3, 1], ![2, 0, 6, 4, 3, 1], ![2, 0, 5, 4, 3, 1]], proof := .tail 191 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6343)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 5, 4, 1], ![2, 0, 6, 5, 3, 1], ![2, 6, 0, 4, 3, 1], ![2, 5, 0, 4, 3, 1]], proof := .tail 98 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6344)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 5, 4, 1], ![2, 0, 6, 5, 3, 1], ![6, 2, 0, 4, 3, 1], ![5, 2, 0, 4, 3, 1]], proof := .tail 197 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6345)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 5, 4, 1], ![2, 6, 0, 5, 3, 1], ![2, 6, 0, 4, 3, 1], ![2, 5, 4, 0, 3, 1]], proof := .tail 378 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6346)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 5, 4, 1], ![2, 6, 0, 5, 3, 1], ![6, 2, 0, 4, 3, 1], ![5, 2, 4, 0, 3, 1]], proof := .tail 378 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6347)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 4, 5, 0, 1], ![2, 0, 6, 5, 4, 1], ![6, 2, 0, 5, 3, 1], ![6, 2, 0, 4, 3, 1], ![5, 4, 2, 0, 3, 1]], proof := .tail 23 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6348)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 5, 4, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 4, 6, 1], ![2, 5, 0, 3, 1, 6], ![2, 4, 0, 3, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 40 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6349)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 4, 6, 1], ![2, 5, 0, 3, 6, 1], ![2, 4, 0, 3, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 377 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6350)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 6, 4, 1], ![2, 5, 0, 6, 3, 1], ![2, 4, 0, 3, 1, 6], ![2, 0, 4, 3, 1, 5]], proof := .tail 166 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6351)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 4, 6, 1], ![2, 5, 0, 3, 6, 1], ![2, 4, 0, 3, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 188 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6352)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 6, 4, 1], ![2, 5, 0, 6, 3, 1], ![2, 4, 0, 3, 6, 1], ![2, 0, 4, 3, 5, 1]], proof := .tail 166 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6353)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 5, 4, 1], ![2, 5, 0, 6, 3, 1], ![2, 4, 0, 6, 3, 1], ![2, 0, 4, 5, 3, 1]], proof := .tail 20 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6354)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 6, 4, 1], ![2, 5, 6, 0, 3, 1], ![2, 4, 0, 3, 1, 6], ![2, 4, 0, 3, 1, 5]], proof := .tail 0 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6355)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 5, 6, 4, 1], ![2, 5, 6, 0, 3, 1], ![2, 4, 0, 3, 6, 1], ![2, 4, 0, 3, 5, 1]], proof := .tail 247 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6356)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 5, 4, 1], ![2, 5, 6, 0, 3, 1], ![2, 4, 0, 6, 3, 1], ![2, 4, 0, 5, 3, 1]], proof := .tail 20 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6357)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 5, 4, 1], ![2, 5, 6, 0, 3, 1], ![2, 4, 6, 0, 3, 1], ![2, 4, 5, 0, 3, 1]], proof := .tail 262 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6358)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 5, 4, 1], ![2, 6, 5, 0, 3, 1], ![2, 6, 4, 0, 3, 1], ![2, 5, 4, 0, 3, 1]], proof := .tail 59 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6359)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 5, 4, 1], ![2, 6, 5, 0, 3, 1], ![6, 2, 4, 0, 3, 1], ![5, 2, 4, 0, 3, 1]], proof := .tail 29 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6360)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 4, 5, 0, 1], ![2, 0, 6, 5, 4, 1], ![6, 2, 5, 0, 3, 1], ![6, 2, 4, 0, 3, 1], ![5, 4, 2, 0, 3, 1]], proof := .tail 381 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6361)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 5, 4, 6, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 5, 4, 6, 1], ![5, 2, 0, 3, 1, 6], ![4, 2, 0, 3, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .low0 (![223, 36, 320, 336, 162, 52, 73, 193, 232, 171, 110, 4, 99, 194, 193, 193, 193, 193, 233, 341, 341, 341, 184, 382, 330, 250, 343, 72]) }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6362)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 5, 4, 6, 1], ![5, 2, 0, 3, 6, 1], ![4, 2, 0, 3, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 339 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6363)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 5, 6, 4, 1], ![5, 2, 0, 6, 3, 1], ![4, 2, 0, 3, 1, 6], ![2, 0, 4, 3, 1, 5]], proof := .tail 141 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6364)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 5, 4, 6, 1], ![5, 2, 0, 3, 6, 1], ![4, 2, 0, 3, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 46 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6365)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 5, 6, 4, 1], ![5, 2, 0, 6, 3, 1], ![4, 2, 0, 3, 6, 1], ![2, 0, 4, 3, 5, 1]], proof := .tail 141 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6366)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 6, 5, 4, 1], ![5, 2, 0, 6, 3, 1], ![4, 2, 0, 6, 3, 1], ![2, 0, 4, 5, 3, 1]], proof := .tail 243 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6367)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 5, 6, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 2, 0, 3, 1, 6], ![2, 4, 0, 3, 1, 5]], proof := .tail 141 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6368)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 5, 6, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 2, 0, 3, 6, 1], ![2, 4, 0, 3, 5, 1]], proof := .tail 141 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6369)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 6, 5, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 2, 0, 6, 3, 1], ![2, 4, 0, 5, 3, 1]], proof := .tail 243 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6370)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 6, 5, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 2, 6, 0, 3, 1], ![2, 4, 5, 0, 3, 1]], proof := .tail 243 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6371)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 0, 5, 6, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 2, 0, 3, 1, 6], ![4, 2, 0, 3, 1, 5]], proof := .low6 (![183, 112, 60, 26, 105, 216, 387, 214, 395, 53, 240, 342, 12, 198, 317, 74, 397, 1, 157, 385, 280, 307, 345, 87, 379, 54, 24, 120]) }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6372)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 0, 5, 6, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 2, 0, 3, 6, 1], ![4, 2, 0, 3, 5, 1]], proof := .tail 246 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6373)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 0, 6, 5, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 2, 0, 6, 3, 1], ![4, 2, 0, 5, 3, 1]], proof := .tail 334 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6374)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 0, 6, 5, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 2, 6, 0, 3, 1], ![4, 2, 5, 0, 3, 1]], proof := .tail 334 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6375)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 5, 4, 0, 1], ![2, 0, 6, 5, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 6, 2, 0, 3, 1], ![4, 5, 2, 0, 3, 1]], proof := .tail 95 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6376)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 5, 4, 0, 1], ![2, 0, 6, 5, 4, 1], ![6, 5, 2, 0, 3, 1], ![6, 4, 2, 0, 3, 1], ![5, 4, 2, 0, 3, 1]], proof := .tail 369 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6377)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 0, 4, 5, 1], ![2, 6, 0, 3, 1, 5], ![2, 6, 0, 3, 1, 4], ![2, 5, 4, 3, 0, 1]], proof := .tail 326 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6378)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 0, 4, 5, 1], ![2, 6, 0, 3, 5, 1], ![2, 6, 0, 3, 4, 1], ![2, 5, 4, 3, 0, 1]], proof := .tail 294 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6379)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 0, 5, 4, 1], ![2, 6, 0, 5, 3, 1], ![2, 6, 0, 4, 3, 1], ![2, 5, 4, 3, 0, 1]], proof := .tail 378 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6380)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 0, 5, 4, 1], ![2, 5, 6, 0, 3, 1], ![2, 4, 6, 0, 3, 1], ![2, 4, 5, 3, 0, 1]], proof := .tail 185 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6381)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 0, 5, 4, 1], ![2, 6, 5, 0, 3, 1], ![2, 6, 4, 0, 3, 1], ![2, 5, 4, 3, 0, 1]], proof := .tail 239 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6382)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 6, 0, 5, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 2, 6, 0, 3, 1], ![2, 4, 5, 3, 0, 1]], proof := .tail 331 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6383)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 0, 4, 5, 1], ![2, 6, 0, 3, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 2, 4, 3, 0, 1]], proof := .tail 326 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6384)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 0, 4, 5, 1], ![2, 6, 0, 3, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 2, 4, 3, 0, 1]], proof := .tail 294 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6385)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 0, 5, 4, 1], ![2, 6, 0, 5, 3, 1], ![6, 2, 0, 4, 3, 1], ![5, 2, 4, 3, 0, 1]], proof := .tail 378 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6386)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 0, 5, 4, 1], ![2, 6, 5, 0, 3, 1], ![6, 2, 4, 0, 3, 1], ![5, 2, 4, 3, 0, 1]], proof := .tail 239 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6387)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 6, 0, 5, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 2, 6, 0, 3, 1], ![4, 2, 5, 3, 0, 1]], proof := .tail 204 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6388)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 0, 4, 5, 1], ![6, 2, 0, 3, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 4, 2, 3, 0, 1]], proof := .tail 326 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6389)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 0, 4, 5, 1], ![6, 2, 0, 3, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 294 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6390)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 0, 5, 4, 1], ![6, 2, 0, 5, 3, 1], ![6, 2, 0, 4, 3, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 261 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6391)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 0, 5, 4, 1], ![6, 2, 5, 0, 3, 1], ![6, 2, 4, 0, 3, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 204 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6392)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 5, 4, 0, 1], ![2, 6, 0, 5, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 6, 2, 0, 3, 1], ![4, 5, 2, 3, 0, 1]], proof := .tail 204 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6393)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 5, 4, 0, 1], ![2, 6, 0, 5, 4, 1], ![6, 5, 2, 0, 3, 1], ![6, 4, 2, 0, 3, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 239 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6394)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 4, 5, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 0, 4, 5, 1], ![6, 2, 0, 3, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 125 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6395)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 5, 4, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 0, 4, 5, 1], ![6, 2, 0, 3, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 310 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6396)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 5, 4, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 0, 5, 4, 1], ![6, 2, 0, 5, 3, 1], ![6, 2, 0, 4, 3, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 150 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6397)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 5, 4, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 0, 5, 4, 1], ![6, 2, 5, 0, 3, 1], ![6, 2, 4, 0, 3, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 150 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6398)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 5, 4, 3, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 0, 5, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 6, 2, 0, 3, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 226 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6399)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (6272 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 6272 ≤ id.val) (hhigh : id.val < 6400) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 6272)) = true := by
  let j : Fin 128 := ⟨id.val - 6272, by omega⟩
  have hsum : 6272 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (6272 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard049
