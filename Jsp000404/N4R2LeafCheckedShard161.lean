import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard161
open N4R2RowDataReplay

-- Original cycle 022871b7118fbe980434a187f2571e612875da1a9963a33775c391e626e413fc; original global index 172.
def localCycle00000 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .triangle 29 1, .triangle 23 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 028ac5a9078985b7628e87d98b9551b560595af7236971b85f8aa148816d1462; original global index 198.
def localCycle00001 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 03bf8c55cdc19a8f8ec1d73e70040be15229ee991e942787a0fb9f987cbfa2a0; original global index 303.
def localCycle00002 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 22 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 05c2e7a2dfbef84b24c7fe857ce7916703856b1aeb4de8f1b30913c2f2c4a2a3; original global index 477.
def localCycle00003 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 067059f7142e388aa0216ffb47e72c7f760582f35afb4cadee335c404a9ec1e8; original global index 528.
def localCycle00004 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .triangle 23 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 07e07c900646a2bc8a3d0495af20dff46f0b701dae8bae333cd309f87a74bf48; original global index 636.
def localCycle00005 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 090fef10a93cbe13890931c17039468f7b9750422a6604c677e3fb584f89df40; original global index 722.
def localCycle00006 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 09aa8c751b0bb7a7625793ec7e3bb2df5a8593c3760b01af1625b1790faa0a3f; original global index 771.
def localCycle00007 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 3]
    constant := ![2, -3, 0, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 8 2, .triangle 11 1]

-- Original cycle 0a1815b80555f571cec55a99d01ef283033d8e472e4159c3f01265f97aa07ca4; original global index 814.
def localCycle00008 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 3 4]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 3 4, .gapUpper 5 5, .gapLower 6 5, .triangle 32 0]

-- Original cycle 0b3943b63bdd84adf2531174d354404678ae0f891c1f388b9ae0015071ef84f2; original global index 898.
def localCycle00009 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 3 6, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 32 1]

-- Original cycle 0d11ac722f87d6f4119998afc450a5c087b6d793b2e398f3d0548a14afdc705a; original global index 1037.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 0ea1ca9c602be97880e1d65d07277656bcb5197aed2e31995cb0f263022ef6d6; original global index 1155.
def localCycle00011 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, 0, 0, -2, 0, 0, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, true, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .gapLower 6 2, .triangle 4 1, .triangle 23 1, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 0f0a145bd3c0b1c54652674226a4c102f4e6e2f05f720680920ce884040ddbb4; original global index 1194.
def localCycle00012 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 2 1, .triangle 22 0, .corridorLower 4 5]

-- Original cycle 0f1693655661b03a61b8c6d007db162f1f0b9970fe6f8f5293e14b2f1095391a; original global index 1199.
def localCycle00013 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 3, .theta 2]
    constant := ![4, -1, -2, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 2 6, .triangle 30 0, .gapLower 6 2, .gapLower 6 1, .triangle 18 1, .triangle 15 0, .corridorLower 2 3]

-- Original cycle 1195319e2cd203f092b3227d732591a88742133c2a8b971c10955121f0f51117; original global index 1403.
def localCycle00014 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 33 0, .triangle 34 0, .gapLower 4 0]

-- Original cycle 15a8e960b0834e6000bd7943b60e0f9c7620e4d92da6068645399189fd7f3e99; original global index 1721.
def localCycle00015 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 169d3f9f7b834ba66fe6be63f09801f2bbeb550c125524ef08e3661b566d7765; original global index 1772.
def localCycle00016 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 2, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 16a240a63c007920c486f6fee79f703fa7b226d6ee9bb47736364f65b1342651; original global index 1774.
def localCycle00017 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 3 5]
    constant := ![2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, true] }
  origin := ![.gapUpper 5 5, .triangle 34 2, .gapLower 6 4, .triangle 33 1]

-- Original cycle 177a2f705819c3079d5ac1791fbf76e686559dd49de7ce2fda31ba890b74d7e7; original global index 1838.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 18af0c03ce29a95db1d959c56053ef4f5c4776a0c86d16517104a0625c22f717; original global index 1930.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 2 1, .triangle 22 0, .corridorLower 4 5]

-- Original cycle 190fc29e8cf2b6fbefb2fa8ef0ebdaff40a3758b811639cddfed8eeec8433e1f; original global index 1955.
def localCycle00020 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .triangle 17 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 1978b20d83a919a5b10ddc8eb2d853394342d3e9320403eba5664fbb66fd29c0; original global index 1988.
def localCycle00021 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 4 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 23 2, .gapLower 6 0]

-- Original cycle 19f83408325594b961d12405c19a12ef161a26f26bf38eed37f10fab5b25be32; original global index 2028.
def localCycle00022 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 6 1, .triangle 5 2, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 1a4c1c685c9b39dbbe57dd324e2e2b8f415e21a6be261ffb011d53f6019525c8; original global index 2054.
def localCycle00023 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 1c178cf563e9911f7db4b991ccd8c5879fa39220b146e87ebbad57f8c2d13ecf; original global index 2168.
def localCycle00024 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 6 2, .triangle 12 0, .corridorLower 4 5]

-- Original cycle 1ceaf6ea1e0e9963916035ac74f269bb539283985d00487862c745eb3d0db074; original global index 2229.
def localCycle00025 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 12 2, .triangle 14 0, .triangle 24 0, .triangle 22 1, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 1e07efbdf79d58566cb59e23543fe75cd583a09e38126219deb97edceed0cf4d; original global index 2309.
def localCycle00026 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .triangle 22 1, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 1f35ddb562819c41d5c95585151c31e2275f966544f77b917d03611517577f1a; original global index 2395.
def localCycle00027 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 1f80d5b15ad7b79e653b5cfc8a875a90612249225eb79872a53d5613a4afcd8e; original global index 2421.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 205ae7c03a3d381c8274a9d5512d8ffdd5c0555d50103bfe387dd54b6607db7d; original global index 2481.
def localCycle00029 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 4 1, .triangle 18 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 214740365bbd99125a55b640ab30f0df281dfbb91996fc9ce37b42731c40b636; original global index 2550.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 217a0f61d52c3f896343f31e37cb1da1a7013a700049c8156dd517450dbf7de7; original global index 2563.
def localCycle00031 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 217cbe4bdc42584a4e190d81e1db49d06631361b0480f9601bb8fb1110f0242f; original global index 2565.
def localCycle00032 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 21c6dbecd8ec202e2b0990707b3d14c123b41b7aab7a68a25f6e08b810e2e3b5; original global index 2589.
def localCycle00033 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 24b729c9f9f3c7c6a8781a9aaf997024973c6c5c32c1bae66df012317a8557bc; original global index 2816.
def localCycle00034 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 30 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 287ebcfa86ef467476633cb2a2193d4cc6a318dc2023126a9ba7e6f31ac0a3cd; original global index 3102.
def localCycle00035 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 3 5]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 33 1]

-- Original cycle 29f1abd47407a63b7691b0f67d1cf94425bfc9ab3b9c8ba5217636c400a6f53e; original global index 3201.
def localCycle00036 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 12 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 2a10bd8f356d2757a13ae9d7da6d990ab1e88e0f0d490c7237c70c21471bd438; original global index 3208.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 2b5dd5079c7c4c0b3e7a1037ac3ea6f26982cc99122b559685a8e19810148e43; original global index 3316.
def localCycle00038 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 4 6, .distance 1 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 23 2, .gapLower 6 2, .gapUpper 4 1]

-- Original cycle 2db31d0509cd97f5d20487fac21e4e9e86a040d0659ec0fddeaf5a0adfde4d21; original global index 3490.
def localCycle00039 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -2, 0, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .gapLower 6 2, .triangle 4 1, .triangle 24 1, .triangle 22 1, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 2e01a496f1190a505f12ae50fb9cd78d9e9a5ccbffa51186b86c1e6ffcbc0347; original global index 3512.
def localCycle00040 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 6, .distance 4 6, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, -1, -1, -2, 2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 24 0, .gapLower 6 0, .gapLower 6 6, .triangle 29 0, .triangle 16 0, .corridorLower 1 2]

-- Original cycle 2e1633e05f967cf8258391e23e392c21fc13c754d9ac54d9441adfe17d340c05; original global index 3521.
def localCycle00041 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 2e878e66c7bbac7e2d1f6fe29fb9b6652be777593ee2f8f82594c9ba0fa1bb71; original global index 3556.
def localCycle00042 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 2f0654f01cc2211058e889d4200ba68e8ec92c6eea9263379f539c244f0f8712; original global index 3597.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 4 6, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 2, -2, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 27 2, .triangle 29 1, .triangle 34 1, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 2f69651f9b3e16fbba046a45f4bb9233acf1aa62efb6264cc4d305efc6a53015; original global index 3625.
def localCycle00044 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 311824bbd4a032feffd3b9ecaefe72ab046ad66611fbcbc50f7d599464fd14a7; original global index 3743.
def localCycle00045 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 4, .distance 0 2, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 25 2, .triangle 6 0, .triangle 0 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 3120eecef2d447cae13260310581fd9586d5e4383dc7e76ff5b5a443c9693fd7; original global index 3746.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 32072d98b3f79b9dd57ba6ebc3e8faa1f857c31c656540c6c734dc3348293603; original global index 3819.
def localCycle00047 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 4, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 2, .triangle 6 2, .triangle 13 0, .triangle 23 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 32c0ed177b60dd9552575b0a46d8b1e8daa4c29d5ed93798d3740d6d992d271d; original global index 3886.
def localCycle00048 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .theta 1]
    constant := ![3, -1, -2, 3, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 27 2, .gapUpper 2 6, .thetaNext 1]

-- Original cycle 3376642a96131b9eeacd645104478b0d06b24e6cd9a6624bcaf042eb97c0c52d; original global index 3937.
def localCycle00049 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 3387f251b329b3e2105cecf2b3b44fc5be10aa62b260a83fd14d264f1715002b; original global index 3941.
def localCycle00050 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 33d81e3a856296882cfcd5a19c384e8e65620d454ea258ceeb04a18074a6d6ed; original global index 3973.
def localCycle00051 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 4 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .gapLower 6 2, .triangle 14 1, .triangle 12 1, .triangle 6 1, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 35574ce519b0a1ea69615a3aca089042b47af89843c7e8f949d63dc879844826; original global index 4086.
def localCycle00052 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 4 2, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle 37c4f03bcfaa1231d1a75304b571a919ac0e96addc7bb7c2dbd86d0db10b9b90; original global index 4288.
def localCycle00053 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .corridorLower 5 6]

-- Original cycle 38bc0a8f9abd5845ec5317bcf74e720015cb051a8bbb2d944a5c5171431fc041; original global index 4365.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 38d70427896da2068a13993ca21595f56275dbe9882763ab3635b4a965a8b9c7; original global index 4375.
def localCycle00055 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .gapLower 6 2, .triangle 4 1, .triangle 18 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 397cdece23ae329b82c8b7e641debe94090475e1c16035ff93ce62b25f4ca4b2; original global index 4430.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 39959331d574fe377abb63405d854292dd44b6eed6cfdd6eb83cf22002bb6768; original global index 4439.
def localCycle00057 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 5 6, .distance 0 5, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 30 1, .triangle 14 0, .triangle 3 1, .triangle 17 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 399d2e697b2e769538577914053a40a97403a4301d1a54cd07763125f64b5374; original global index 4443.
def localCycle00058 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 3b9a922c34e93b43374b507fa83bce3bbbf684931c56ff0c713395d108168766; original global index 4605.
def localCycle00059 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 27 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 3d93ac90057f6c0f8bfb0725d45b5410e6ac949eac5d595b019cc977928d7858; original global index 4767.
def localCycle00060 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 8 2, .gapLower 6 1, .gapLower 6 0]

-- Original cycle 3dc55e1dcd3f1f2b9316350e702e64a65f7953465e3260943991d81e955c1af1; original global index 4782.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 41ffb90561b23f97d5049094496907fbc341b0018fdd28365ce9a09921a48df6; original global index 5085.
def localCycle00062 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 4 6, .distance 3 6, .distance 0 6, .distance 1 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![4, -2, 0, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 4 6, .gapLower 6 4, .triangle 11 2, .gapLower 6 1, .triangle 23 1, .triangle 22 0, .corridorLower 4 5]

-- Original cycle 42db32180f6a395f8a2d8ffc8f4a0a16b6c378591ea2bbee4008de5183819c33; original global index 5146.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 27 2, .triangle 29 1, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 44b68075261c529e17bf2307384cf26c2eabfa9aee7a52c7deb8333c17053063; original global index 5326.
def localCycle00064 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 31 0, .triangle 28 0, .triangle 6 0, .triangle 5 2, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .gapLower 3 0]

-- Original cycle 452a47ad1eaed52a29541673c9edd208a3a137a7ea83002d4d835e7f1df390ac; original global index 5350.
def localCycle00065 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 46041f8a12c6555640d94ea725e07513d33c0d8e9c79a58671379e4016d2edec; original global index 5417.
def localCycle00066 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 6 1, .triangle 8 0, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 47219a1a9c35dc3ff926ca2c2dd1d9c696b73dcb9f097c9c37221c4c8c03e57f; original global index 5516.
def localCycle00067 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 6 2, .triangle 12 0, .corridorLower 4 5]

-- Original cycle 482406c8d08e30a502eace6471d4b63a88488df400947077d7add59a570a0901; original global index 5585.
def localCycle00068 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 4850a2ee7f8a873993d255c916a36d1ea18d65c55c7fb4e7246db5b2289dcf59; original global index 5598.
def localCycle00069 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![4, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 18 2, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 485612164ff286b7bc24d45ff29bfca68287565da5a4ed921e2a8a5b8546ea3c; original global index 5601.
def localCycle00070 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .triangle 23 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 486fc5d3f5561ce675dac1c010d98d0b548e53c93d224a60cfc375aa88a19ea7; original global index 5609.
def localCycle00071 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 4 6, .distance 0 4, .distance 0 2]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .triangle 13 0, .triangle 6 1]

-- Original cycle 48cdc4aa21da9de576e322766112d51742abb0acf5842efcbae029c27d9e681a; original global index 5641.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 0 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 13 2, .gapLower 6 2, .triangle 23 1, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 4ad7bb9f7290892a4b1a772d7de2f91413e90b8b82aa579fe38716e2360b5889; original global index 5812.
def localCycle00073 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 29 1, .gapLower 6 2, .triangle 14 1, .triangle 12 1, .triangle 6 1, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 4caded7ec9b914246d347288090bea7642ba357cfeebb1674b821272458f4b95; original global index 5950.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 4e3ff41bdb569f658315d0ee4f69554004f3c7776c364348799cbb48261b9ee2; original global index 6075.
def localCycle00075 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 2, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 4f5b875a1284a609c3f4a3b8b555f849c49838b343d3a38cef56adc625199839; original global index 6168.
def localCycle00076 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 0 6, .distance 0 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 2, .gapLower 6 3, .triangle 13 1]

-- Original cycle 4fb6edf5c20d2771e5c0fe364d38c83cce9d0976bdae39be84d58a6110455a75; original global index 6190.
def localCycle00077 : Cycle where
  length := 3
  data := {
    node := ![.theta 5, .distance 5 6, .theta 6, .theta 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 0, .gapLower 6 0, .thetaNext 5]

-- Original cycle 4ff183a4951005fca814222b66a967e466c596d82d20848c94807efc85464553; original global index 6207.
def localCycle00078 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 503d44398aa82617751b27b59a9c01a3b4ae3086daafb4b3db26ed0a54a09810; original global index 6229.
def localCycle00079 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 50c9e5f343ac77a5f4e6a9e35be2069cc0d6843b190732de605cc64389cd6fdf; original global index 6274.
def localCycle00080 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 0 6, .distance 0 2]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .triangle 8 1]

-- Original cycle 514479d390c9942ccb6eed61bf24e93778896f39cd182ea0807908b16832d73b; original global index 6319.
def localCycle00081 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![4, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .gapLower 4 5, .triangle 6 0, .triangle 5 0, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .gapLower 3 0]

-- Original cycle 532d3829197547293a1b44a69c741c222419b9314436ce5666a3088752d3fa6d; original global index 6473.
def localCycle00082 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 2]
    constant := ![-1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 15 0, .triangle 27 0, .triangle 32 1, .gapUpper 4 1, .triangle 16 1]

-- Original cycle 53813114e08b82e2eee0bbfbd02d12d52bf4e2101adab9df18642f6794033963; original global index 6490.
def localCycle00083 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 0 2, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -2, 2, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .gapLower 6 6, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 6 0, .triangle 0 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 550c276925058888a8d53df36016989d4793f79dc6a33dcb0949c3423ff0a1b3; original global index 6587.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 56004518c65f60aac00eff074008988c66f1b3c13e541fb2d8c4460d08035cea; original global index 6671.
def localCycle00085 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 568b64c94cc95c9dd53cdb7e12f1e6f49e400420471e7a1feb5b540d477bad0a; original global index 6710.
def localCycle00086 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .gapLower 6 2, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 592c979471e620bbcc5f695e3f0e20e413ab0beaf84c932976450b7ca132ace0; original global index 6916.
def localCycle00087 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Original cycle 5c3ecec023570ace9d4fcd7651d844cef3148c3450d8dbe99a0ceda6460f1154; original global index 7182.
def localCycle00088 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 2, .gapLower 6 2, .triangle 14 1]

-- Original cycle 5cd004ff388addd16ba64966a13846868cbbbaf125267f59abbade8a9a8ef2fc; original global index 7223.
def localCycle00089 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 6, .distance 0 3]
    constant := ![2, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 29 1, .gapLower 6 3, .triangle 11 1]

-- Original cycle 5cd61694f127c91fed896dec404671b9d1eeba015dbeff17de906b69cd8da802; original global index 7225.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 600484377827f76afa4ab0e280ebcf70af8c361be123ac841208df9b7e63cc5e; original global index 7485.
def localCycle00091 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 60bed6256c79f75d2c3404c8a72dc27ed045ee2b736ce1d429391d8b319f56db; original global index 7534.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 60dda3183b5fe504dc7c309061f97c4d99d4d91e13f67c456a8e07fb2f2e8e27; original global index 7550.
def localCycle00093 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 3]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .triangle 11 1]

-- Original cycle 63ccae85c2513ab4cadac12307b664356e4c8efdf03d7fead0a1aeb1829638df; original global index 7778.
def localCycle00094 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .gapLower 6 3, .triangle 23 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 6620e6a611e669eb130282c4ce9903f1509e00e9d7ed01387b588a08b78340a2; original global index 7946.
def localCycle00095 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -3, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 6837905f812d15c047e199d09522a49aebfb21f5ada3ab0bddf2f6c8deb769d4; original global index 8103.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .triangle 8 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 6a34c3384a1366012f2175b2bb7fe49b839469b4de32dd662c1dcf1fb40d6c78; original global index 8268.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .triangle 30 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 6bda24ffc6d8e2d0098af6cec9d716b395301b056108bb4b9a795ecbbc499008; original global index 8402.
def localCycle00098 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 23 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 6cca98ddcd30eec2d546a1f2070bbb1e0d628a2650fbcf2aef61b7a1f5e7c1aa; original global index 8466.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 6e0f28d66a0ae3bc21379dd710e158564c951b04d2617e1c1d16c1d25a0da786; original global index 8545.
def localCycle00100 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 28 1, .triangle 6 0, .triangle 0 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 6e26227795882704a7b7a06e251697d3cf8265f58ad32ad94c9aff56920b8875; original global index 8551.
def localCycle00101 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 4 0]

-- Original cycle 6ee7189c9058ace790d31830958ebfb057c7dfa00b3a69ef9192ff72027cedc9; original global index 8603.
def localCycle00102 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 4 6, .distance 0 4, .distance 0 2]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .triangle 13 0, .triangle 6 1]

-- Original cycle 6f0d902f602fcf9753a7a20e37a6b7e4915f24289c18482072169082e522ab41; original global index 8612.
def localCycle00103 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .triangle 18 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 6f52a793329b5c7d120a9795d3572306347b9d2bd5a8b01cee0eb16c26d06d05; original global index 8630.
def localCycle00104 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .gapLower 6 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 6f94f0b10b3b7a5fb74d250c594c7234a4ec01488dc420e4b3fc562f329f45d9; original global index 8653.
def localCycle00105 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 23 1, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 70063b995be684dda0021a1edcbe5cefa187c2f5e9a96c324af6825b3a71ba10; original global index 8682.
def localCycle00106 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 5 6, .theta 6, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -2, -2, 0, 3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 707e93db357412224c4d6965f33b104322fc255db61655d37c95037b146348c3; original global index 8715.
def localCycle00107 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 5 6, .triangle 22 0, .triangle 23 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 7392202e6d87dba69c029b881985fbb851cda3df6cf8d8385c2c8712d7e415c6; original global index 8960.
def localCycle00108 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -3, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 4 1, .triangle 18 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 73f03b5db40a9bda194ee6893fbe8d7c59c4af735e4cff0f3e27e7ac079fe85d; original global index 8992.
def localCycle00109 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 8 2, .triangle 13 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 7a61a228e97ca90faede2ac639cd94b97903237d73e741446061960b47d4ee47; original global index 9468.
def localCycle00110 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, true, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 14 0, .triangle 3 1, .triangle 22 1, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 7a7cf0547b93446529ad44ce46f5d6ab360d18ba68dbdf7a6c22fd9be1f63230; original global index 9476.
def localCycle00111 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 2, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 7b7faf316ac15257e0bc1520a192b509eb09e463307e743db4003400c6901d4f; original global index 9557.
def localCycle00112 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 7cc5b77f7a37f9df1e0c248c48adda039326a8fc96cd6876375bd33cd98fb286; original global index 9665.
def localCycle00113 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 7d38663c958002412161497f4726bb6479611bc59151d46d3111b9af40a88d1f; original global index 9705.
def localCycle00114 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 30 0, .gapLower 2 4, .triangle 6 0, .triangle 0 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 7d9a5fe4ae9dfa53eb839809fb930eccb36cedcc14d1416db240baa91f22f2b2; original global index 9748.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 7e288f5d32c0a54ce241fa1715457a1638716314ce592bcab7958d66e0718e90; original global index 9801.
def localCycle00116 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 4 2, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle 8099574f2c5d3bbf6ad57298964237c65a848b7484bee1ec1a3d626c819d8af0; original global index 9982.
def localCycle00117 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, 0, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, true, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 2, .triangle 30 0, .triangle 14 0, .triangle 3 1, .triangle 22 1, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 80f0bbb6b6257188f3156fd91768fcdc2644dc24a7a5844e82dcdb2eed202343; original global index 10006.
def localCycle00118 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 5 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 813de2638225c2b338408d068511417f572bd761cc1be7320a95d855484d56fb; original global index 10031.
def localCycle00119 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 4, .distance 4 5, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 6 2, .triangle 12 0, .triangle 22 0, .gapLower 4 0]

-- Original cycle 8146a41e428bdc1e2bd43e8ce49d2550b3dbaff5318f73838a1e403a69a762f9; original global index 10037.
def localCycle00120 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -3, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .gapLower 6 2, .triangle 4 1, .triangle 18 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 81b3376ad3dd0a8f1ad23bb23b37e706535d22255e10adae992b963519ed8184; original global index 10069.
def localCycle00121 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 4 1, .gapLower 6 2, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 8524c5ef5f752180703ece070635db0d2a47d6f55161065084077d58a8150f28; original global index 10331.
def localCycle00122 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .gapLower 6 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 8651aa78cda6ac96d40430b1ac70ce2b94f2e2d6a640ab9bd5fa2504a32f0293; original global index 10414.
def localCycle00123 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 2, .triangle 29 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 87ef0d373bf60409f15f10e9b7f3d7f8b1de0312a309c71edb3671b30cd2a11d; original global index 10534.
def localCycle00124 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -3, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 8826604953e81dcff0a985d0b4976406b1276bbfb478110358f1184c2d7c1cc9; original global index 10552.
def localCycle00125 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 8960750056a90036ad408eb70f94bbb233b900e20195221922e02569a3dff5e6; original global index 10628.
def localCycle00126 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 4 6, .distance 0 6, .distance 0 2]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .gapLower 6 3, .triangle 8 1]

-- Original cycle 89bdaa29e88c45635285df408217752fe42f69c9a70a9b6ad248e189bfc15d87; original global index 10671.
def localCycle00127 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 9 1, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 8abae896c7c40451626531f1439c16f1374a2ec491e1fca5089cbeab7a490d72; original global index 10749.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 12 0, .triangle 22 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 8b3d7e26bb0591d10e16447f6d9a54c5597eca9b205cf30b36c7aacfc3c13f35; original global index 10788.
def localCycle00129 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 3 4]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 3 4, .gapUpper 5 5, .gapLower 6 5, .triangle 32 0]

-- Original cycle 8cad17885010e0f5e2be494ff6cb09b8de89d4a17fbdbab4c54e43b2d0952077; original global index 10881.
def localCycle00130 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 23 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 8d0299a616085f8a70c830f282e34572a4fa097eb93f4de5f11ec30b92bd2f56; original global index 10906.
def localCycle00131 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 28 1, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 8d7ffe5d26075cc8b2e3e37a3956e3936dac7d520ece9d38ce22430a097c68d8; original global index 10941.
def localCycle00132 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 29 1, .triangle 23 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 8debfabe7c7b8d3d96245a84b40fccd7761d95f7eb2279939268665b675ec5ae; original global index 10988.
def localCycle00133 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 2, 0, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 8e49fad6e8e0ef1596b6e940fe57534dce4b99c397869d779d292c6d3d2ade82; original global index 11015.
def localCycle00134 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 8e5f537528192d620e0a58215bd0158f52959b1678a924d1ad08271c4063abc3; original global index 11021.
def localCycle00135 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Original cycle 8ef6c1a600ac409ff10a14d3a5d605c6c99c114c5a983aff12653626f9fd2b5c; original global index 11060.
def localCycle00136 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle 8fe4e5d09c4071f52791a6cbeea6d80b6303d26cfda46f59ae8c76cb85d34bc5; original global index 11138.
def localCycle00137 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 12 0, .triangle 22 0, .triangle 16 1, .triangle 15 2, .triangle 21 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 902b6d1f99a3b91aed2d083d9d33aaf5b5cd8c2fcb9c398f7465d54817c53b39; original global index 11157.
def localCycle00138 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -2, 2, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .gapLower 6 6, .triangle 32 0, .triangle 25 2, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 9363c5492a97ec8e8ba9e41bc6217120d8c42551c9999c28ff89ca246da1e707; original global index 11432.
def localCycle00139 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 16 1, .triangle 15 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 937ec22db98ddeeca3e034033861c7cbe6761ba7aef79e944bcf62d0a6e6474c; original global index 11443.
def localCycle00140 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 4 1, .triangle 23 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 943e04f726932779e18d20ddcaafdacdcf2058411b735a8c87157baa8f7d58eb; original global index 11501.
def localCycle00141 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .triangle 23 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 94bde2ea139b323a43c305bbfa224617bf00ecf2d3cec489681e53fd3e5f1315; original global index 11543.
def localCycle00142 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 31 0, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 18 0, .triangle 15 0, .gapLower 3 0]

-- Original cycle 9848e08626216ab76544ece9120b9ead6dfea743fd39db87759bce88c709e1b0; original global index 11828.
def localCycle00143 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 98e99ef1026f4e3aedccfeca264faf5a3b06eaeb23cc259dda0f83856e3396d2; original global index 11872.
def localCycle00144 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 994c99f3b7736bed44fe8b09d554e92a01a031e7768c0761d7579ce08525a9ef; original global index 11902.
def localCycle00145 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 4 6]

-- Original cycle 9acee481269359eb7be5d7c7d5f065d21e5bfaaf3af0344b6b7b9b566edbd8d7; original global index 12030.
def localCycle00146 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .corridorLower 4 6, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 9ae95b0348c82b43a860217f3bfc6631801bfbacff122a7882aafb76ac2a859b; original global index 12038.
def localCycle00147 : Cycle where
  length := 5
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .theta 6]
    constant := ![3, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 0]

-- Original cycle 9b1b423134ba8714cbdcb6de8faaf6661df10f8a9ca79acc69da28fba0eafe14; original global index 12058.
def localCycle00148 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, 0, -2, 0, 0, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, true, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 27 2, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 9c088b2bbaaf4f3f5362a47fff68e9369e93c831e85d16f5e7844be43657ec61; original global index 12137.
def localCycle00149 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 9def9ab8e867f920ba55a5167da0908b06db450ffcdf7e8de6a05a82196389a0; original global index 12291.
def localCycle00150 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 6 0, .triangle 0 1, .triangle 15 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 9e8269f1c95a9c521a339ad678f779d6d7ff8af51076ecf39dff5f9003b36326; original global index 12346.
def localCycle00151 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .theta 1]
    constant := ![3, -1, -2, 3, 0, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapUpper 2 6, .thetaNext 1]

-- Original cycle a05040488fc6803ff68bd24a843c63e6a4d0d7e3f44babf9d343c15a313a1ae6; original global index 12474.
def localCycle00152 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 27 1, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle a272b3b9a44b254748929730a4b8cec02f078fda65f9bf6f46f0e3c94333dc62; original global index 12636.
def localCycle00153 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 5 6, .distance 0 5, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, -1, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .gapLower 6 3, .triangle 14 0, .triangle 3 1, .triangle 22 1, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle a811e52c743462052c0d849f77d7e9a9264272dd93017707ded69d395923be6b; original global index 13089.
def localCycle00154 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 23 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle a9707215f99a8e69d5fcd6ef958d61def534f35a301e1e20c240afc21aadd29c; original global index 13190.
def localCycle00155 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 3 6, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 33 1]

-- Original cycle a9854fd6829e729c9d19775ecdb167b29916973c6a55ec02d3c2559653f837db; original global index 13196.
def localCycle00156 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle a9884a1571b84d367efd9766e849f1a9f25a65f7cf1ea4f593a766ddc31792c2; original global index 13198.
def localCycle00157 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 12 0, .triangle 22 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ac3bf4c00cd4731ecc41409427980efa7f213b1e04cdd7aa4c414a38456b8e62; original global index 13426.
def localCycle00158 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 2 4, .distance 0 2, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 29 1, .triangle 6 0, .triangle 0 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ad9380ef221d3513763bb2f915a14a0b18d8579408aaedf3aabfc3bd720c2a44; original global index 13547.
def localCycle00159 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 23 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ada019554a3531290bb52f3c1f31fdb754b68b97ed8a716c54cc6d1d6f4e942c; original global index 13551.
def localCycle00160 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .corridorLower 4 6, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle ae0d3e85487a3700c2f89194323281ab4f27357163cd310e32a75bdaf2626b95; original global index 13581.
def localCycle00161 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle ae9ecca350a927690670819e975070f69286feec68dbbf7f8786271c80ce6d8e; original global index 13629.
def localCycle00162 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 22 1, .triangle 16 1, .triangle 15 2, .triangle 21 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle aec44c21233c49725093d48389517b1aa49bc46bb034b1c80ebd0bb858070e2f; original global index 13641.
def localCycle00163 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapLower 6 2, .triangle 13 1, .triangle 6 1, .corridorLower 0 2, .thetaLower 0]

-- Original cycle af0d6e9717ad64d30d3c037f28f7017d827030706c2e7ec10522896a9d2196ca; original global index 13666.
def localCycle00164 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .gapLower 6 2, .triangle 4 1, .gapLower 6 0]

-- Original cycle b03d9b358ba261450161128af0ba14d81262cac98e0aebac00fed2f07b954126; original global index 13759.
def localCycle00165 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 29 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle b0628e7dcc912587adb5fe9c812f4014fafac68f848d28cd5b4c0580712b4ebf; original global index 13770.
def localCycle00166 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 8 2, .gapLower 6 1, .triangle 23 1, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle b06807bb8af933de6053584c6bdd46171478698ac2d8b9426b8a661af6aee68c; original global index 13773.
def localCycle00167 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b07a386ebd982d5b7a1757fbebaeec49e4178e4c4ba57ea225525a5bce4cf7c9; original global index 13779.
def localCycle00168 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b193d891f2c03f198fa0a38d0aa1049092719bede1a61dbfa64658c930796627; original global index 13879.
def localCycle00169 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle b1eea7d2405f0c7b41e3e14a93d9d6b51aeafd10d85315ba6c13f83cbf5798f5; original global index 13905.
def localCycle00170 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -3, 3, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle b2491943d197ba0bc82128db08407f1eb6a5a55167c9cc35bbc455f3fb10989e; original global index 13933.
def localCycle00171 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 2 4, .distance 4 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 3, .theta 2]
    constant := ![4, -1, -2, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 2 6, .triangle 29 0, .gapLower 6 2, .gapLower 6 1, .triangle 18 1, .triangle 15 0, .corridorLower 2 3]

-- Original cycle b2865a885d9c3605b9801447664e2f6b1da80f7ea799eb1c28fc8b858a409f7c; original global index 13952.
def localCycle00172 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle b2aeb8d62fabb2cf23ae8b7e02871564b4bead1a2ec17291a6c92ba633c9d4c7; original global index 13964.
def localCycle00173 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 3 5, .distance 2 5, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -2, 2, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .gapLower 6 6, .triangle 33 0, .triangle 26 2, .triangle 28 1, .triangle 22 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle b50fa235b2e93d0310608b62e429469aee5c95944d85ac41219e33e04dcc2cac; original global index 14142.
def localCycle00174 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle b54f7167de24137e001e7c3f7fc19fbccca477025f3a966b9aec786b9fa9b1b2; original global index 14165.
def localCycle00175 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b5cca5d71862705d4a53426379172d9e6000e7b227c4f491f894949615ddc51a; original global index 14202.
def localCycle00176 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 0 2, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .triangle 28 0, .triangle 6 0, .triangle 0 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle b7d7d3b824c913286857a32405b2c2cc9bb9c87724d33e0359fa3954eccbb822; original global index 14345.
def localCycle00177 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 5 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Original cycle b9b752cdc10c21a77d30ea4a685f38ad54c69a1e4221ce48297cf98d30c098c6; original global index 14495.
def localCycle00178 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 4, .distance 0 2, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 0 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle b9ebff5033e4a10ce1a602bc12b3793aa557b9a5f0cdae420ca364d5b30862c8; original global index 14517.
def localCycle00179 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle ba6af48a4380f505c67fca5b574ebfee59fe96c9d93656155599c1b973ff9cdf; original global index 14557.
def localCycle00180 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 5 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 14 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle be4e0437d3d3ab28e33ffa145500b174c77c1d6f1bae88f86487f5969d054878; original global index 14846.
def localCycle00181 : Cycle where
  length := 4
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .theta 6]
    constant := ![3, -2, 0, -2]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 21 2, .gapLower 6 0]

-- Original cycle bf91fb8936374623f76b136e4ab4f8a091e2da2ff584086ea4c4b08e9c0ceed5; original global index 14946.
def localCycle00182 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .gapLower 2 4, .triangle 6 0, .triangle 0 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c06933ab5e687f4b73edbf4f818fe4d26fe16404971578cade06bff334d63174; original global index 15020.
def localCycle00183 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .triangle 4 1, .triangle 18 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c23ca354016c7b2323196faa9a03a8624fd05eeb06915ab430bcfef022939b5d; original global index 15166.
def localCycle00184 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -3, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .gapLower 6 2, .triangle 4 1, .triangle 18 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c45710ba464254eed41ec402b7aaa2679f35c7baba449adb59abdf2fafef5f8a; original global index 15316.
def localCycle00185 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle c5af06551b5aa3dd87522f4c3ed36e33bb70719e8758d2aa7fc56cd3ae11e74c; original global index 15418.
def localCycle00186 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 30 1, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c8361b88013dbefe2e409ca810ee8915ffd73a14489cd88839bdd5300788c6e5; original global index 15626.
def localCycle00187 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle ca334ae103ac250529d05d38236f233e3dc13ff7e427b4ac914ad949fc01754d; original global index 15802.
def localCycle00188 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -3, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 3 2, .triangle 14 2, .gapLower 6 2, .triangle 18 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle ca8a061bbed47eb5c653e74878c9b7064402c1f33f335bb5d3e4fc127689a276; original global index 15829.
def localCycle00189 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 1, .gapUpper 5 1]

-- Original cycle ca8d61feaed15b56f25b6299b6edf1f9586285f24d1c31f9f545c17b2a7ff820; original global index 15831.
def localCycle00190 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 4 6, .distance 4 5, .distance 0 4, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 29 1, .triangle 34 1, .triangle 12 0, .triangle 2 1, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ce14ce208c2ddd2c153bc589c63b901a88d66c5a6a45d34430cf5bd209ddac03; original global index 16101.
def localCycle00191 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 34 1, .triangle 22 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle ce938c55adebddcb03c92dcd3533ec92192a827ccc8db1126d7c76bb15885dac; original global index 16133.
def localCycle00192 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 5 6]

-- Original cycle cfb8e2544ec97e0ea43942dc5b696a695f44cd3a6e3cb7e4954e763be5d23a97; original global index 16211.
def localCycle00193 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 3 6, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 5, .gapLower 6 4, .triangle 32 1]

-- Original cycle d0a1772125925fbb8ffd2912d2deecbcdb68cc1138f98ef80252d7c72b322e58; original global index 16282.
def localCycle00194 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle d2d1641ce0fad402b1094c609153211229f71c2e4f284ddecda6fc835c417b3d; original global index 16447.
def localCycle00195 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle d32cae771064c5cd1d0fb8621fd98956496f4013c39a812353f2d93263e4d99d; original global index 16473.
def localCycle00196 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle d3db8e01e6380e2915ea236ebe2bfe9cb13d575621db7b13812215bf4e5e1602; original global index 16537.
def localCycle00197 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d52dd7b84b467bb867cd14c5f6c6e5053e96a5886fd1676f0f4b342259acdc67; original global index 16635.
def localCycle00198 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle d5f6e6370af3bf19bdd1ee75be4e8c2b99bcf153da5ce7ad330468d6ea6fe888; original global index 16698.
def localCycle00199 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 4 1, .triangle 23 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle d86cae73076a506432988586315ff23bff96aa1641de3ec8585051aa5e95b25f; original global index 16895.
def localCycle00200 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 6 2, .triangle 12 0, .triangle 22 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle d907d6b4ac0e8270719bd47b7e3fba4e5fb3995a768ec735ef61d271a83cc6ae; original global index 16952.
def localCycle00201 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 13 0, .triangle 2 1, .triangle 22 0, .corridorLower 4 5]

-- Original cycle d9106b7820e5aa7dd4891181beb6f94b971264a4f2c2da532f6d96ba6b3c6dcf; original global index 16956.
def localCycle00202 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle d92fd58ec59e4fa894e532e563e39c6f92dce48eccc582ac21a0912c12bc9e1b; original global index 16969.
def localCycle00203 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 8 2, .triangle 13 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle da69852488a536a21484495f5100e7d3325288d63003274cb75ee831fecd2bd7; original global index 17069.
def localCycle00204 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 3, .triangle 23 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle db4810ff8e93366af5a42f5bf31f85f23e70badd30d2632e68987c921d68a1a7; original global index 17139.
def localCycle00205 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 2, .gapLower 6 1, .triangle 23 1, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle dcebfb4f0ae63391cc5583e6243cdee7a54b26c778be87bb38b483d5d3455fe8; original global index 17267.
def localCycle00206 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 4, .distance 0 3]
    constant := ![2, -2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .triangle 13 0, .triangle 9 1]

-- Original cycle dd2e7f07159adb71b49f9fe1319cd7d41983642985102bdb8936d40da35ef841; original global index 17294.
def localCycle00207 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle dd65d7739b13ed7a3d03d04915c28dd6d070604d5ec64222da862eabadff69fb; original global index 17308.
def localCycle00208 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 0 2, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 28 0, .triangle 6 0, .triangle 0 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle de971f97a2f2f3a033ef2cf623be98265dc315eb998793858da3bf96929e4088; original global index 17407.
def localCycle00209 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 2 6, .distance 4 6, .distance 2 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 29 2, .gapLower 6 3, .gapUpper 4 4]

-- Original cycle e028d93cd204bff7cc0cc8813ebd336c21ab78735b3118ce93241833277080bd; original global index 17522.
def localCycle00210 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle e17fd3dcf6098daca56b2e4d163e76f5fa0ec08dddf350668bde161426becf45; original global index 17635.
def localCycle00211 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 3, .theta 2]
    constant := ![4, -2, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 2 6, .gapLower 6 2, .gapLower 6 1, .triangle 18 1, .triangle 15 0, .corridorLower 2 3]

-- Original cycle e1ce91f1720c1a4ae911636f045300c4d9f7c11843023c6c34d4b5662e9df220; original global index 17657.
def localCycle00212 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .gapLower 6 1, .corridorLower 1 6, .thetaLower 1]

-- Original cycle e212f83718d8d71f4fa0f75e2a9e701b7e097f83eeedcfb9c0a064fdbdad545c; original global index 17677.
def localCycle00213 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 3, .triangle 23 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle e2d5ea5e717fe6bb6221bc7d49e98afba06066861c11776d9a703686d49e48dc; original global index 17742.
def localCycle00214 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 1, 0, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .triangle 8 0, .triangle 0 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle e4d5b2ad5066aa7f6b2a0199839ff68c4d5ec13fa1908e8b34c753103522b0fa; original global index 17888.
def localCycle00215 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .gapLower 6 1, .corridorLower 1 6, .thetaLower 1]

-- Original cycle e587a24b80c5221b4f1458074afb4746719cadd7c933731992032a61c0f1e570; original global index 17953.
def localCycle00216 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 0 2]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 5 2, .gapUpper 3 3, .gapLower 6 5, .triangle 8 0]

-- Original cycle e759fe51c4ec9c28593a21743be1a025aee351665dde537eec4c803890cef56f; original global index 18096.
def localCycle00217 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle e7ebec6e9c76d00cc5ab8a8e12f59ed6fe993d9311a8e44247f915b85656c1e3; original global index 18136.
def localCycle00218 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle e8d73106310bba4bb05a378b1f9033dd4a3fb56ffb9b7822ad80a72f4042abb9; original global index 18199.
def localCycle00219 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 29 1, .corridorLower 4 6]

-- Original cycle e92136fcae60dade4d490859ccf5fbbac45b17206cc4aa8a613ce55b3595c6bc; original global index 18218.
def localCycle00220 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 2 6, .distance 5 6, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 30 2, .gapLower 6 3, .gapUpper 5 3]

-- Original cycle ec758505c1dad9a3f06f68240f4bd933f33a845fdcdf4ab03a22af4748bdbfe6; original global index 18456.
def localCycle00221 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle ec7e76ea63c9cb2705e65426619fe5245bd421d211f5a1e7f4293cf4918387e8; original global index 18462.
def localCycle00222 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 4 0]

-- Original cycle ed77e966dfb64c8194aa2b5d10bb19fb2d47d94ee73c836dab79345d2fc7d5d7; original global index 18536.
def localCycle00223 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle f05dcef4f37e0615eccff7fa1fbdc2a26699986d7eac039cf888461dd81105bf; original global index 18743.
def localCycle00224 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 22 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle f2250f6c7991ac0423aadce80670ff1d3ef65e63add0b47d2d32ed265f78eb89; original global index 18882.
def localCycle00225 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle f3c6220ee036775892337abe467cd79d149724c01f62562a2d7ccb7dd0009f90; original global index 19016.
def localCycle00226 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle f7d45f5af07f519f8cefeea1def90e3cf76a50c2aa83009a3d0103abf20da21e; original global index 19319.
def localCycle00227 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -3, 3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle f8d28dee201feb750d83d9214d30da50f249f8626ed142d1e9c331ebf2724117; original global index 19408.
def localCycle00228 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle f99ece6ca02db51cc335d67d5ce7b6c268e6c31b66360fc503fe21fb451535f0; original global index 19460.
def localCycle00229 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 8 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle fc4efce37cacb96bb38b2d2649896c3096c49b0ae7e750527d261a1785fce7b0; original global index 19708.
def localCycle00230 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![4, -2, 0, -2, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .gapLower 6 4, .triangle 27 2, .gapLower 6 2, .triangle 4 1, .triangle 23 1, .triangle 22 0, .corridorLower 4 5]

-- Original cycle ff6e03fdc9105aa89eef350eef274b706fd4622f19830a0c4e3b1adaac14906d; original global index 19971.
def localCycle00231 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 5, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 2, .triangle 14 2, .gapLower 6 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

def library : Library := fun id => if id < 116 then (if id < 58 then (if id < 29 then (if id < 14 then (if id < 7 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 5 then (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)) else (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)))) else (if id < 10 then (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))) else (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none))))) else (if id < 21 then (if id < 17 then (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none))) else (if id < 19 then (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)))) else (if id < 25 then (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none))) else (if id < 27 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none)))))) else (if id < 43 then (if id < 36 then (if id < 32 then (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none))) else (if id < 34 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)))) else (if id < 39 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))) else (if id < 41 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none))))) else (if id < 50 then (if id < 46 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))) else (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)))) else (if id < 54 then (if id < 52 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none))) else (if id < 56 then (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none))))))) else (if id < 87 then (if id < 72 then (if id < 65 then (if id < 61 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))) else (if id < 63 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)))) else (if id < 68 then (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none))) else (if id < 70 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none))))) else (if id < 79 then (if id < 75 then (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none))) else (if id < 77 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none)))) else (if id < 83 then (if id < 81 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none))) else (if id < 85 then (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none)) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)))))) else (if id < 101 then (if id < 94 then (if id < 90 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none))) else (if id < 92 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)))) else (if id < 97 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none))) else (if id < 99 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))))) else (if id < 108 then (if id < 104 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none))) else (if id < 106 then (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none)))) else (if id < 112 then (if id < 110 then (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none)) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none))) else (if id < 114 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none)))))))) else (if id < 174 then (if id < 145 then (if id < 130 then (if id < 123 then (if id < 119 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none))) else (if id < 121 then (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none)) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none)))) else (if id < 126 then (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none))) else (if id < 128 then (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none))))) else (if id < 137 then (if id < 133 then (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none))) else (if id < 135 then (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)))) else (if id < 141 then (if id < 139 then (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none)) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none))) else (if id < 143 then (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none)) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none)))))) else (if id < 159 then (if id < 152 then (if id < 148 then (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none))) else (if id < 150 then (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none)) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none)))) else (if id < 155 then (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none))) else (if id < 157 then (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none)) else (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none))))) else (if id < 166 then (if id < 162 then (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none))) else (if id < 164 then (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none)) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none)))) else (if id < 170 then (if id < 168 then (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none)) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none))) else (if id < 172 then (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id = 171 then some localCycle00171 else none)) else (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id = 173 then some localCycle00173 else none))))))) else (if id < 203 then (if id < 188 then (if id < 181 then (if id < 177 then (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none))) else (if id < 179 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id = 178 then some localCycle00178 else none)) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none)))) else (if id < 184 then (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id = 183 then some localCycle00183 else none))) else (if id < 186 then (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id = 185 then some localCycle00185 else none)) else (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id = 187 then some localCycle00187 else none))))) else (if id < 195 then (if id < 191 then (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none))) else (if id < 193 then (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none)) else (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none)))) else (if id < 199 then (if id < 197 then (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none)) else (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id = 198 then some localCycle00198 else none))) else (if id < 201 then (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id = 200 then some localCycle00200 else none)) else (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none)))))) else (if id < 217 then (if id < 210 then (if id < 206 then (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none))) else (if id < 208 then (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none)) else (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none)))) else (if id < 213 then (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id = 212 then some localCycle00212 else none))) else (if id < 215 then (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id = 214 then some localCycle00214 else none)) else (if id < 216 then (if id = 215 then some localCycle00215 else none) else (if id = 216 then some localCycle00216 else none))))) else (if id < 224 then (if id < 220 then (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id = 219 then some localCycle00219 else none))) else (if id < 222 then (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id = 221 then some localCycle00221 else none)) else (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id = 223 then some localCycle00223 else none)))) else (if id < 228 then (if id < 226 then (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id = 225 then some localCycle00225 else none)) else (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id = 227 then some localCycle00227 else none))) else (if id < 230 then (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id = 229 then some localCycle00229 else none)) else (if id < 231 then (if id = 230 then some localCycle00230 else none) else (if id = 231 then some localCycle00231 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 2, 5, 3, 4, 0], ![6, 1, 5, 3, 0, 4], ![6, 5, 1, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 3, 1, 2, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 135 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20608)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![2, 6, 5, 3, 4, 0], ![1, 6, 5, 3, 0, 4], ![6, 5, 1, 2, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 3, 1, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 149 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20609)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 2, 5, 3, 4, 0], ![6, 1, 5, 3, 0, 4], ![6, 5, 1, 2, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 3, 1, 2, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 68 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20610)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 3, 0, 4, 6], ![5, 1, 2, 0, 4, 6], ![5, 1, 0, 2, 3, 6], ![4, 3, 2, 1, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 177 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20611)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 3, 0, 4, 6], ![5, 1, 2, 0, 6, 4], ![5, 1, 0, 2, 6, 3], ![4, 3, 2, 1, 0, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 118 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20612)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 3, 0, 6, 4], ![5, 1, 2, 0, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 3, 2, 1, 0, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 195 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20613)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 3, 0, 6, 4], ![5, 1, 2, 0, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 195 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20614)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![5, 2, 3, 6, 4, 0], ![5, 1, 3, 0, 6, 4], ![5, 1, 2, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 0, 2, 3, 5]], proof := .tail 195 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20615)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 3, 6, 0, 4], ![5, 1, 2, 0, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 152 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20616)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![5, 2, 3, 6, 4, 0], ![5, 1, 3, 6, 0, 4], ![5, 1, 2, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 152 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20617)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 3, 6, 0, 4], ![5, 1, 2, 6, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 74 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20618)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 6, 3, 0, 4], ![5, 1, 6, 2, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![1, 4, 3, 2, 0, 5]], proof := .tail 202 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20619)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![5, 2, 3, 6, 4, 0], ![5, 1, 3, 6, 0, 4], ![5, 1, 2, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 74 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20620)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![5, 2, 3, 6, 4, 0], ![5, 1, 6, 3, 0, 4], ![5, 1, 6, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 3, 2, 0, 5]], proof := .tail 202 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20621)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![5, 2, 6, 3, 4, 0], ![5, 1, 6, 3, 0, 4], ![5, 6, 1, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 3, 1, 2, 0, 5]], proof := .tail 202 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20622)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![5, 6, 2, 3, 4, 0], ![5, 6, 1, 3, 0, 4], ![5, 6, 1, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 5]], proof := .tail 6 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20623)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 3, 6, 0, 4], ![5, 1, 2, 6, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 2, 1, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 228 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20624)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 6, 3, 0, 4], ![5, 1, 6, 2, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 2, 1, 6, 0], ![1, 4, 3, 2, 5, 0]], proof := .tail 58 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20625)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![5, 2, 3, 6, 4, 0], ![5, 1, 3, 6, 0, 4], ![5, 1, 2, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 6, 0], ![4, 1, 2, 3, 5, 0]], proof := .tail 228 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20626)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![5, 2, 3, 6, 4, 0], ![5, 1, 6, 3, 0, 4], ![5, 1, 6, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 6, 0], ![4, 1, 3, 2, 5, 0]], proof := .tail 58 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20627)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![5, 2, 6, 3, 4, 0], ![5, 1, 6, 3, 0, 4], ![5, 6, 1, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 6, 0], ![4, 3, 1, 2, 5, 0]], proof := .tail 58 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20628)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![5, 6, 2, 3, 4, 0], ![5, 6, 1, 3, 0, 4], ![5, 6, 1, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 5, 0]], proof := .tail 6 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20629)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 2, 3, 4, 0], ![5, 6, 1, 3, 0, 4], ![5, 6, 1, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 6, 1, 0], ![4, 3, 2, 5, 1, 0]], proof := .tail 42 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20630)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 2, 3, 4, 0], ![6, 5, 1, 3, 0, 4], ![5, 6, 1, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 6, 2, 1, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 81 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20631)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 2, 3, 4, 0], ![6, 5, 1, 3, 0, 4], ![6, 5, 1, 2, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 3, 2, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 14 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20632)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 2, 3, 4, 0], ![6, 5, 1, 3, 0, 4], ![6, 5, 1, 2, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 3, 2, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 143 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20633)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![3, 2, 4, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 4, 5, 6], ![2, 1, 0, 4, 5, 6], ![1, 0, 2, 3, 5, 6], ![1, 0, 2, 3, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 45 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20634)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![3, 2, 4, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 4, 5, 6], ![2, 1, 0, 4, 5, 6], ![1, 0, 2, 3, 6, 5], ![1, 0, 2, 3, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 131 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20635)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![3, 2, 4, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 4, 5, 6], ![2, 1, 0, 4, 6, 5], ![1, 0, 2, 3, 6, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 3, 4]], proof := .tail 100 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20636)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![3, 2, 4, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 4, 6, 5], ![2, 1, 0, 4, 6, 5], ![1, 0, 2, 3, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 3, 4]], proof := .low6 (![3, 116, 88, 220, 210, 9, 172, 30, 104, 180, 217, 187, 138, 13, 52, 52, 212, 52, 115, 34, 97, 55, 192, 53, 153, 15, 57, 63]) }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20637)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![3, 2, 4, 6, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 4, 6, 5], ![2, 1, 0, 4, 6, 5], ![1, 0, 2, 3, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 3, 4]], proof := .tail 99 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20638)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![3, 2, 4, 6, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 0, 4, 6, 5], ![2, 1, 0, 4, 6, 5], ![1, 0, 2, 3, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low6 (![77, 189, 188, 108, 210, 9, 172, 106, 231, 18, 90, 49, 40, 96, 225, 226, 27, 167, 161, 61, 196, 72, 92, 223, 148, 229, 158, 63]) }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20639)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![3, 2, 4, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 4, 5, 6], ![2, 1, 0, 6, 4, 5], ![1, 0, 2, 6, 3, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 4, 3]], proof := .tail 182 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20640)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![3, 2, 4, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 4, 6, 5], ![2, 1, 0, 6, 4, 5], ![1, 0, 2, 6, 3, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 4, 3]], proof := .tail 218 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20641)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![3, 2, 4, 6, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 4, 6, 5], ![2, 1, 0, 6, 4, 5], ![1, 0, 2, 6, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 4, 3]], proof := .tail 218 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20642)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![3, 2, 4, 6, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 0, 4, 6, 5], ![2, 1, 0, 6, 4, 5], ![1, 0, 2, 6, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 4, 3]], proof := .tail 218 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20643)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![3, 2, 4, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 4, 5], ![1, 0, 6, 2, 3, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 4, 2, 3]], proof := .tail 20 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20644)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![3, 2, 4, 6, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 4, 5], ![1, 0, 6, 2, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 4, 2, 3]], proof := .tail 91 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20645)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![3, 2, 4, 6, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 4, 5], ![1, 0, 6, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 4, 2, 3]], proof := .tail 32 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20646)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![3, 2, 6, 4, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 4, 5], ![1, 6, 0, 2, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 0, 2, 3]], proof := .tail 47 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20647)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![3, 2, 6, 4, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 4, 5], ![1, 6, 0, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 0, 2, 3]], proof := .tail 47 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20648)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![3, 2, 6, 4, 5, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 0, 2, 3]], proof := .low6 (![113, 112, 38, 4, 80, 7, 214, 31, 111, 70, 199, 203, 65, 107, 141, 140, 109, 5, 86, 121, 69, 16, 94, 213, 103, 93, 29, 216]) }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20649)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![3, 6, 2, 4, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 0, 4, 5], ![2, 1, 0, 6, 4, 5], ![1, 6, 0, 2, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 2, 0, 3]], proof := .tail 10 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20650)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![3, 6, 2, 4, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 0, 4, 5], ![2, 1, 0, 6, 4, 5], ![1, 6, 0, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 2, 0, 3]], proof := .tail 10 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20651)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![3, 6, 2, 4, 5, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 0, 4, 5], ![2, 1, 0, 6, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 2, 0, 3]], proof := .tail 10 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20652)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![3, 6, 2, 4, 5, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 0, 4, 5], ![2, 1, 0, 6, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 2, 1, 0, 3]], proof := .tail 28 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20653)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 3, 2, 4, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 4, 5], ![1, 6, 0, 2, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 2, 3, 0]], proof := .tail 156 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20654)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 3, 2, 4, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 4, 5], ![1, 6, 0, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 2, 3, 0]], proof := .tail 156 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20655)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![6, 3, 2, 4, 5, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 2, 3, 0]], proof := .tail 156 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20656)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![6, 3, 2, 4, 5, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 0, 4, 5], ![2, 1, 6, 0, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 2, 1, 3, 0]], proof := .tail 154 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20657)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![6, 3, 2, 4, 5, 1], ![6, 3, 2, 4, 5, 0], ![3, 6, 1, 0, 4, 5], ![2, 6, 1, 0, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 179 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20658)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![6, 3, 2, 4, 5, 1], ![6, 3, 2, 4, 5, 0], ![6, 3, 1, 0, 4, 5], ![6, 2, 1, 0, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 46 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20659)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![3, 2, 4, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 4, 5, 6], ![2, 1, 0, 5, 4, 6], ![1, 0, 2, 5, 3, 6], ![1, 0, 2, 4, 3, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 79 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20660)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![3, 2, 4, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 4, 5, 6], ![2, 1, 0, 5, 6, 4], ![1, 0, 2, 5, 6, 3], ![1, 0, 2, 4, 3, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 176 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20661)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![3, 2, 4, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 4, 5, 6], ![2, 1, 0, 6, 5, 4], ![1, 0, 2, 5, 6, 3], ![1, 0, 2, 4, 6, 3], ![1, 0, 2, 4, 5, 3]], proof := .tail 208 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20662)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![3, 2, 4, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 4, 5, 6], ![2, 1, 0, 6, 5, 4], ![1, 0, 2, 6, 5, 3], ![1, 0, 2, 6, 4, 3], ![1, 0, 2, 5, 4, 3]], proof := .tail 114 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20663)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![3, 2, 4, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 4, 6, 5], ![2, 1, 0, 6, 5, 4], ![1, 0, 2, 6, 5, 3], ![1, 0, 6, 2, 4, 3], ![1, 0, 5, 2, 4, 3]], proof := .tail 117 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20664)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![3, 2, 4, 6, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 4, 6, 5], ![2, 1, 0, 6, 5, 4], ![1, 0, 2, 6, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 0, 2, 4, 3]], proof := .tail 26 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20665)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![3, 2, 4, 6, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 0, 4, 6, 5], ![2, 1, 0, 6, 5, 4], ![1, 0, 2, 6, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 0, 2, 4, 3]], proof := .tail 178 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20666)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![3, 2, 4, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 5, 4], ![1, 0, 6, 2, 5, 3], ![1, 0, 6, 2, 4, 3], ![1, 0, 5, 4, 2, 3]], proof := .tail 56 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20667)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![3, 2, 4, 6, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 5, 4], ![1, 0, 6, 2, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 0, 4, 2, 3]], proof := .tail 56 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20668)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![3, 2, 4, 6, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 5, 4], ![1, 0, 6, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 0, 4, 2, 3]], proof := .tail 175 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20669)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![3, 2, 6, 4, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 5, 4], ![1, 6, 0, 2, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 4, 0, 2, 3]], proof := .tail 130 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20670)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![3, 2, 6, 4, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 5, 4], ![1, 6, 0, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 4, 0, 2, 3]], proof := .tail 130 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20671)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![3, 2, 6, 4, 5, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 1, 0, 2, 3]], proof := .tail 75 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20672)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![3, 6, 2, 4, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 0, 4, 5], ![2, 1, 0, 6, 5, 4], ![1, 6, 0, 2, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 4, 2, 0, 3]], proof := .tail 142 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20673)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![3, 6, 2, 4, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 0, 4, 5], ![2, 1, 0, 6, 5, 4], ![1, 6, 0, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 4, 2, 0, 3]], proof := .tail 142 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20674)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![3, 6, 2, 4, 5, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 0, 4, 5], ![2, 1, 0, 6, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 142 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20675)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![3, 6, 2, 4, 5, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 0, 4, 5], ![2, 1, 0, 6, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 165 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20676)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![6, 3, 2, 4, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 5, 4], ![1, 6, 0, 2, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 4, 2, 3, 0]], proof := .tail 64 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20677)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![6, 3, 2, 4, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 5, 4], ![1, 6, 0, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 4, 2, 3, 0]], proof := .tail 64 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20678)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![6, 3, 2, 4, 5, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 64 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20679)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![6, 3, 2, 4, 5, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 0, 4, 5], ![2, 1, 6, 0, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 219 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20680)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 3, 2, 4, 5, 1], ![6, 3, 2, 4, 5, 0], ![3, 6, 1, 0, 4, 5], ![2, 6, 1, 0, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 219 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20681)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![6, 3, 2, 4, 5, 1], ![6, 3, 2, 4, 5, 0], ![6, 3, 1, 0, 4, 5], ![6, 2, 1, 0, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 150 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20682)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![3, 2, 4, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 5, 4, 6], ![2, 1, 0, 5, 4, 6], ![1, 0, 5, 2, 3, 6], ![1, 0, 4, 2, 3, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 2 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20683)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![3, 2, 4, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 5, 4, 6], ![2, 1, 0, 5, 6, 4], ![1, 0, 5, 2, 6, 3], ![1, 0, 4, 2, 3, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 136 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20684)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![3, 2, 4, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 5, 4, 6], ![2, 1, 0, 6, 5, 4], ![1, 0, 5, 2, 6, 3], ![1, 0, 4, 2, 6, 3], ![1, 0, 2, 4, 5, 3]], proof := .tail 224 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20685)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![3, 2, 4, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 4], ![1, 0, 5, 6, 2, 3], ![1, 0, 4, 2, 3, 6], ![1, 0, 4, 2, 3, 5]], proof := .low6 (![227, 116, 184, 209, 95, 155, 23, 44, 122, 21, 147, 181, 173, 171, 52, 52, 215, 52, 51, 73, 123, 39, 145, 159, 204, 50, 190, 43]) }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20686)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![3, 2, 4, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 6, 5, 4], ![1, 0, 5, 6, 2, 3], ![1, 0, 4, 2, 6, 3], ![1, 0, 4, 2, 5, 3]], proof := .tail 134 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20687)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![3, 2, 4, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![1, 0, 5, 6, 2, 3], ![1, 0, 4, 6, 2, 3], ![1, 0, 4, 5, 2, 3]], proof := .tail 207 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20688)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![3, 2, 4, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![1, 0, 6, 5, 2, 3], ![1, 0, 6, 4, 2, 3], ![1, 0, 5, 4, 2, 3]], proof := .tail 110 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20689)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![3, 2, 4, 6, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![1, 0, 6, 5, 2, 3], ![1, 6, 0, 4, 2, 3], ![1, 5, 0, 4, 2, 3]], proof := .tail 25 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20690)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![3, 2, 4, 6, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![1, 0, 6, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 1, 0, 4, 2, 3]], proof := .low6 (![77, 189, 84, 76, 71, 7, 0, 54, 221, 174, 102, 216, 1, 197, 37, 102, 216, 169, 185, 102, 216, 105, 126, 89, 183, 206, 102, 216]) }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20691)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![3, 2, 6, 4, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![1, 6, 0, 5, 2, 3], ![1, 6, 0, 4, 2, 3], ![1, 5, 4, 0, 2, 3]], proof := .tail 98 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20692)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![3, 2, 6, 4, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![1, 6, 0, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 1, 4, 0, 2, 3]], proof := .tail 98 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20693)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![3, 2, 6, 4, 5, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![6, 1, 0, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 4, 1, 0, 2, 3]], proof := .tail 144 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20694)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![3, 6, 2, 4, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![1, 6, 0, 5, 2, 3], ![1, 6, 0, 4, 2, 3], ![1, 5, 4, 2, 0, 3]], proof := .tail 98 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20695)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![3, 6, 2, 4, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![1, 6, 0, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 1, 4, 2, 0, 3]], proof := .tail 98 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20696)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![3, 6, 2, 4, 5, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![6, 1, 0, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 66 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20697)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![3, 6, 2, 4, 5, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![6, 1, 0, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 87 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20698)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![6, 3, 2, 4, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![1, 6, 0, 5, 2, 3], ![1, 6, 0, 4, 2, 3], ![1, 5, 4, 2, 3, 0]], proof := .tail 132 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20699)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![6, 3, 2, 4, 5, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![1, 6, 0, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 1, 4, 2, 3, 0]], proof := .tail 132 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20700)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![6, 3, 2, 4, 5, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![6, 1, 0, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 22 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20701)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![6, 3, 2, 4, 5, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![6, 1, 0, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 127 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20702)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 3, 2, 4, 5, 1], ![6, 3, 2, 4, 5, 0], ![3, 6, 1, 0, 5, 4], ![2, 6, 1, 0, 5, 4], ![6, 1, 0, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 162 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20703)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 3, 2, 4, 5, 1], ![6, 3, 2, 4, 5, 0], ![6, 3, 1, 0, 5, 4], ![6, 2, 1, 0, 5, 4], ![6, 1, 0, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 139 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20704)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![3, 2, 5, 4, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 5, 4, 6], ![2, 1, 0, 5, 4, 6], ![1, 5, 0, 2, 3, 6], ![1, 4, 0, 2, 3, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 194 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20705)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![3, 2, 5, 4, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 5, 4, 6], ![2, 1, 0, 5, 6, 4], ![1, 5, 0, 2, 6, 3], ![1, 4, 0, 2, 3, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 200 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20706)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![3, 2, 5, 4, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 5, 4, 6], ![2, 1, 0, 6, 5, 4], ![1, 5, 0, 2, 6, 3], ![1, 4, 0, 2, 6, 3], ![1, 0, 2, 4, 5, 3]], proof := .tail 119 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20707)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![3, 2, 5, 4, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 0, 2, 3, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 157 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20708)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![3, 2, 5, 4, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 6, 5, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 0, 2, 6, 3], ![1, 0, 4, 2, 5, 3]], proof := .tail 101 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20709)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![3, 2, 5, 4, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 0, 6, 2, 3], ![1, 0, 4, 5, 2, 3]], proof := .tail 222 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20710)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![3, 2, 5, 6, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 0, 2, 3, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 191 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20711)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![3, 2, 5, 6, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 6, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 0, 2, 6, 3], ![1, 4, 0, 2, 5, 3]], proof := .tail 168 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20712)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![3, 2, 5, 6, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 0, 6, 2, 3], ![1, 4, 0, 5, 2, 3]], proof := .tail 125 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20713)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![3, 2, 6, 5, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 6, 0, 2, 3], ![1, 4, 5, 0, 2, 3]], proof := .tail 198 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20714)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![3, 2, 6, 5, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![1, 6, 5, 0, 2, 3], ![1, 6, 4, 0, 2, 3], ![1, 5, 4, 0, 2, 3]], proof := .tail 36 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20715)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![3, 2, 6, 5, 4, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![1, 6, 5, 0, 2, 3], ![6, 1, 4, 0, 2, 3], ![5, 1, 4, 0, 2, 3]], proof := .tail 128 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20716)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![3, 2, 6, 5, 4, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 0, 2, 3], ![5, 4, 1, 0, 2, 3]], proof := .tail 78 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20717)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![3, 6, 2, 5, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 6, 0, 2, 3], ![1, 4, 5, 2, 0, 3]], proof := .tail 186 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20718)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![3, 6, 2, 5, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![1, 6, 5, 0, 2, 3], ![1, 6, 4, 0, 2, 3], ![1, 5, 4, 2, 0, 3]], proof := .tail 36 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20719)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![3, 6, 2, 5, 4, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![1, 6, 5, 0, 2, 3], ![6, 1, 4, 0, 2, 3], ![5, 1, 4, 2, 0, 3]], proof := .tail 41 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20720)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![3, 6, 2, 5, 4, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 0, 2, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 160 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20721)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![3, 6, 2, 5, 4, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 0, 2, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 78 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20722)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 6, 0, 2, 3], ![1, 4, 5, 2, 3, 0]], proof := .tail 33 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20723)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![1, 6, 5, 0, 2, 3], ![1, 6, 4, 0, 2, 3], ![1, 5, 4, 2, 3, 0]], proof := .tail 36 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20724)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![1, 6, 5, 0, 2, 3], ![6, 1, 4, 0, 2, 3], ![5, 1, 4, 2, 3, 0]], proof := .tail 85 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20725)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 0, 2, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 146 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20726)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 0, 2, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 78 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20727)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![6, 3, 2, 4, 5, 0], ![3, 6, 1, 0, 5, 4], ![2, 6, 1, 0, 5, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 0, 2, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 137 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20728)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![6, 3, 2, 4, 5, 0], ![6, 3, 1, 0, 5, 4], ![6, 2, 1, 0, 5, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 0, 2, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 82 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20729)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![3, 2, 5, 4, 6, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 0, 5, 4, 6], ![2, 1, 0, 5, 4, 6], ![5, 1, 0, 2, 3, 6], ![4, 1, 0, 2, 3, 6], ![1, 0, 2, 3, 4, 5]], proof := .low6 (![170, 116, 120, 124, 193, 8, 23, 60, 164, 151, 48, 129, 83, 211, 166, 62, 129, 205, 163, 230, 129, 11, 17, 129, 133, 35, 59, 129]) }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20730)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![3, 2, 5, 4, 6, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 0, 5, 4, 6], ![2, 1, 0, 5, 6, 4], ![5, 1, 0, 2, 6, 3], ![4, 1, 0, 2, 3, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 67 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20731)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![3, 2, 5, 4, 6, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 0, 5, 4, 6], ![2, 1, 0, 6, 5, 4], ![5, 1, 0, 2, 6, 3], ![4, 1, 0, 2, 6, 3], ![1, 0, 2, 4, 5, 3]], proof := .tail 24 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20732)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![3, 2, 5, 4, 6, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 0, 2, 3, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 12 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20733)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![3, 2, 5, 4, 6, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 0, 2, 6, 3], ![1, 0, 4, 2, 5, 3]], proof := .tail 19 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20734)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![3, 2, 5, 4, 6, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 0, 6, 2, 3], ![1, 0, 4, 5, 2, 3]], proof := .tail 201 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20735)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (20608 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 20608 ≤ id.val) (hhigh : id.val < 20736) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 20608)) = true := by
  let j : Fin 128 := ⟨id.val - 20608, by omega⟩
  have hsum : 20608 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (20608 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard161
