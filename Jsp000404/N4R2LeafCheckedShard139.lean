import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard139
open N4R2RowDataReplay

-- Original cycle 00003cf531cd1bc460ce306f0a158fd54a909c49f8facf3c685a23fcae4ea7e1; original global index 0.
def localCycle00000 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 0 5, .distance 5 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 7 2, .triangle 14 0, .gapLower 6 2, .triangle 23 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 00425d1d4ca58e61748b4b161ec769eee545b3c3b13df13cdbaf0ff9875dd09e; original global index 23.
def localCycle00001 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 4, .triangle 13 1, .gapUpper 4 3]

-- Original cycle 006dcab8a01bd0c39e209bc28717dacc21e70220bd89fbecdfad62e00ba0be18; original global index 37.
def localCycle00002 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 00cc1ec0e0c48eb1f7c20d9ed75310f7b6af1ce0f3a13b60913513cc577a257f; original global index 73.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 5, .distance 5 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 2, .triangle 7 2, .triangle 14 0, .triangle 24 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 0118e80104e090ec02e26637fa0d135c4e3cfe55d19f7384610b679f50d51eb5; original global index 96.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 0, .triangle 5 0, .triangle 0 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 0130a48129bb00f46ae517495b7d86e1363f04c288e4fe1273ed4237532e799e; original global index 106.
def localCycle00005 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .triangle 13 1, .triangle 34 1, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 017cd4f53c1a3fab84647abebec28672a8c25ce4f790bf3e587d34a2434773d6; original global index 124.
def localCycle00006 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 01fe1a3d5144eee48839f36d0f2341a864e4890ae0f5ede0472d196241d3d611; original global index 160.
def localCycle00007 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 27 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 022bc14e0c31fcb70ac2d503c2faa80b16bc288803b926d410f955f0c8d64fa2; original global index 173.
def localCycle00008 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 0 6, .distance 0 3, .distance 0 2]
    constant := ![2, 0, 0, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, true, false] }
  origin := ![.gapUpper 2 2, .triangle 8 2, .triangle 11 1, .gapLower 0 1]

-- Original cycle 02656d49b4f37cd8a906e3742cc638e9b08f8dbd311c90a8029354692950c155; original global index 188.
def localCycle00009 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .gapLower 6 4, .triangle 13 1, .triangle 23 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 026a7c6a1cac203de327d22e5a101e8b7f33e67fc840110d715449ba293a7bda; original global index 189.
def localCycle00010 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 26 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 028ac5a9078985b7628e87d98b9551b560595af7236971b85f8aa148816d1462; original global index 198.
def localCycle00011 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 0337e16bc23b49c18be6af82a89b7579454a89f4a8957e848f56581ff8000152; original global index 258.
def localCycle00012 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 27 2, .gapLower 6 2, .triangle 13 1, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 03c308ed0862df00ab5ac39023c62c72e3a7792528d2306a300d217985db8c4d; original global index 305.
def localCycle00013 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 03f0e1f79d5a7628fd071484e95d6263a3a62504552c5434812bac2126145d11; original global index 314.
def localCycle00014 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 0411c070d8fb803b74ed0ef055f038002a7cd080a7ae812d3ebd368558298959; original global index 319.
def localCycle00015 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 5 6, .distance 2 5, .distance 2 3]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 30 0, .gapLower 2 3]

-- Original cycle 056d16e9480388d90d72c59e665d81b5002ccc3b926f48aae477cdbe9e777d2a; original global index 441.
def localCycle00016 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4]
    constant := ![4, 0, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 15 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5]

-- Original cycle 0589b737ce22e6ce8dfe627fc2763fe6b70678c94e43f8af57728e79107082ef; original global index 451.
def localCycle00017 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 05c2e7a2dfbef84b24c7fe857ce7916703856b1aeb4de8f1b30913c2f2c4a2a3; original global index 477.
def localCycle00018 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 05f1614cc6044ad0ede21cd5b651fae0dce18077c0919054082e0c42e03b96e1; original global index 492.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 061dfbd8e51f32209bf2880a858cc1d1a26ef13d6b5ceb09b63afbc2fa9e6c54; original global index 505.
def localCycle00020 : Cycle where
  length := 3
  data := {
    node := ![.theta 0, .distance 0 1, .theta 1, .theta 0]
    constant := ![2, -2, 0]
    coefficient := ![1, -1, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 6, .gapUpper 1 6, .thetaNext 0]

-- Original cycle 0635dbb42f4d3fd49ab076e5cbf9ceb9fd0ad00ca804db43d95174afe18268d9; original global index 512.
def localCycle00021 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -2, -1, 2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 1, -1, 0]
    strict := ![false, false, true, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 12 0, .gapLower 0 2, .corridorLower 0 3, .gapLower 0 6, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 066131c6e4fb0fc8b72a23369c098a2fe983b396039789799308c070fc3c4718; original global index 524.
def localCycle00022 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 2, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 06a24465f2cc7199dc48e92b47798e638731fc38a389af4d877ec5083eccc496; original global index 546.
def localCycle00023 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 14 1, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 0715a645ec98da82f1953aa20ab1d0fd69ea69afa1a6a9f63920b33bbbded671; original global index 584.
def localCycle00024 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 0 5, .distance 0 6, .distance 4 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 7 2, .triangle 14 2, .gapLower 6 3, .triangle 23 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 073eec2dc4fbdf6d35ffbd2f5cfaf33537cfe0d2628ea1ee36ec0ce4f0380cbd; original global index 596.
def localCycle00025 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 2 4, .distance 2 3, .distance 0 2, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 29 1, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 07e07c900646a2bc8a3d0495af20dff46f0b701dae8bae333cd309f87a74bf48; original global index 636.
def localCycle00026 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 0834bcb07ae67b42fc6fdd38b5e89fafa12f52033c2a72b2439bbcfb537b81ec; original global index 656.
def localCycle00027 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 2 6, .distance 2 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 27 1]

-- Original cycle 085fd3585f8c10d8f26929089f8b4242a04c24c1ae0994b11f11aea25cbf8563; original global index 665.
def localCycle00028 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 0871e7124286714f68d278ad4f6a3b0281210b71d6a21313ab4ba3aa6701ae67; original global index 673.
def localCycle00029 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 088dd3e030f62a961b2d9be7b0135700e119b4e5831e7cbe39640277b08eb235; original global index 680.
def localCycle00030 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 2, .theta 0, .distance 0 1, .distance 0 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -2, 2, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 3, .triangle 5 0, .gapLower 0 0, .gapLower 0 6, .triangle 2 2, .triangle 13 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 091f1f62c14c6b0198710dc61d723763bfb0cf8c7bbd1cb9ec2c4f00f1687b4a; original global index 728.
def localCycle00031 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 095800b454161b7d4f75e17a91d04de918e39c915343f1a7fec0fd810f25383b; original global index 745.
def localCycle00032 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 5, .distance 1 5, .distance 1 2, .theta 1]
    constant := ![3, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .gapLower 0 4, .gapLower 5 1, .triangle 17 1, .corridorLower 1 2]

-- Original cycle 096dfe9806fc56e65ce38c99e5f6f4763bf3dccf19bd990563273f3e9fe57d31; original global index 749.
def localCycle00033 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![-3, 0, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 0 5, .gapLower 4 3, .triangle 23 2, .gapUpper 1 5]

-- Original cycle 09d7224f0768c30a8ea051c98d142d9b244811ec2bb890f7879fcd3c08c8b8a4; original global index 792.
def localCycle00034 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .gapLower 6 4, .triangle 13 2, .triangle 14 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle 0a1815b80555f571cec55a99d01ef283033d8e472e4159c3f01265f97aa07ca4; original global index 814.
def localCycle00035 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 3 4]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 3 4, .gapUpper 5 5, .gapLower 6 5, .triangle 32 0]

-- Original cycle 0a4c629ae52891a3fa3bdd7d5901dd289b8ea5092cc6269c09547e5d579a0aa2; original global index 823.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 3, .distance 3 5, .theta 5]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 24 2, .triangle 4 0, .triangle 0 0, .triangle 15 0, .triangle 26 0, .gapLower 5 0]

-- Original cycle 0a5786efd40b46064c3fab02b857cfda851ce87c0aee37afd52d99faed0b6980; original global index 825.
def localCycle00037 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 2 6, .distance 5 6, .distance 2 5]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 30 2, .gapLower 6 4, .gapUpper 5 4]

-- Original cycle 0ab76ed79aa5b25e2560ab0157564a7f967f0c65a568b1840e50d87b1f007729; original global index 852.
def localCycle00038 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 0 6, .distance 4 6, .distance 1 6, .theta 1]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 12 2, .triangle 14 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 1 6]

-- Original cycle 0b09b6e108f54dcb5dbcc35903349567fc15359867c4e2951748e5504dbe068c; original global index 883.
def localCycle00039 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 13 2, .gapLower 6 2, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 0b3943b63bdd84adf2531174d354404678ae0f891c1f388b9ae0015071ef84f2; original global index 898.
def localCycle00040 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 3 6, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 32 1]

-- Original cycle 0b9b7312a6616fada91ac310e632fe68723517ea3cebddb8d58985cdac830074; original global index 929.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 5 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 0c4a062c25144b3c6b0c2948e63127cf41cf4685a3e2bb70014a833fca784554; original global index 971.
def localCycle00042 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .gapLower 6 3, .corridorLower 5 6]

-- Original cycle 0c5335c3ed925f8bcd130e3297040ca1f920c332084010cf78181bdbcf2a344e; original global index 975.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -3, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 14 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 0c77cbc3e0fee5465773d0afb2ab0c253ae75a4bf1cf9ab4deccead9aa194ff5; original global index 989.
def localCycle00044 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 0c80827b77617bb33757fa86e671f3ef5c83ddf730ca84f21e612abaca4e4e1e; original global index 990.
def localCycle00045 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .gapLower 6 0]

-- Original cycle 0c8bd5c71b94c4724322fce4a26c8c9ad699afcfef29a92e3b137fe32213ddee; original global index 993.
def localCycle00046 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .triangle 8 2, .triangle 4 1, .gapLower 6 1, .gapLower 6 0]

-- Original cycle 0cf28ce60a6e362b47b8010c7c0bffbdc3871882c9a39e49644a116208bacc47; original global index 1020.
def localCycle00047 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![4, -1, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 5 6, .triangle 12 0, .triangle 13 0, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 0d0f46bfa95409c1728b9f644ef2d801330908667d048ca0f620f3cc9602df8d; original global index 1033.
def localCycle00048 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 0d15817fce83e339c15ba50cd3a87580be6b0827a146d10ee632cddfda0810e0; original global index 1039.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 0 6, .distance 4 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, -1, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 13 1, .triangle 34 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle 0e2acb7a0f10df173aaa3daf8aeda3d353673424f3b7efaabc6196979ff5b6c2; original global index 1116.
def localCycle00050 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 5 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 0e307303a4a75df1c4f6b22eb7279a2f58e6a0982e9093b3a8ea29a0ec8743d6; original global index 1117.
def localCycle00051 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 3]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 3 2, .triangle 11 2, .gapLower 0 2]

-- Original cycle 0e58244fc4ff2089deab0e98b01d542f9796e7cf82c28ee5c0a36833399245ea; original global index 1131.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 4, .distance 0 5, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0]
    constant := ![2, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.gapLower 0 6, .triangle 2 2, .gapLower 0 4, .gapLower 5 3, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0]

-- Original cycle 0f0a145bd3c0b1c54652674226a4c102f4e6e2f05f720680920ce884040ddbb4; original global index 1194.
def localCycle00053 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 2 1, .triangle 22 0, .corridorLower 4 5]

-- Original cycle 0fe118597fc798b65fa70a7584468826b8042bf1a37cba5f665f1f62bb5ed1d4; original global index 1267.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, -1, -3, 3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2]

-- Original cycle 103cb625db53e4e2282479cca7d2e34c38349654ffcda0035e01a72bc5dd2f7a; original global index 1306.
def localCycle00055 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 13 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 11582afcbec38829de0f1c3d41c60d85cb3203c6c8d00aa336dffb6411d10ef8; original global index 1379.
def localCycle00056 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0]
    constant := ![2, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .gapLower 4 3, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0]

-- Original cycle 119645f3c2e5883ad8e93dd3f33e38d3e05e1a73ace374dab9ed9db4e2352718; original global index 1404.
def localCycle00057 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 2, .gapLower 6 5, .triangle 18 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 11c5a69b52c7afc4117696324b2a51d368c40ef01b3dfb6417072c5f23d932ad; original global index 1413.
def localCycle00058 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 2 6, .distance 5 6, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 30 2, .gapLower 6 4, .gapUpper 5 4]

-- Original cycle 12126553d818e444b1379250cb01db447e687b19ff30cb57b720d9ba8fea9c48; original global index 1443.
def localCycle00059 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .gapLower 5 2, .gapLower 0 3, .triangle 6 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 130f6803a53121e59ab2ef11e5bb46cb4ea924ff03132435f193662a2c378936; original global index 1507.
def localCycle00060 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 13a5ece5ad05d26941b494a1b7c02cd1b04b5c80969cfdcebb2d167690d8f2df; original global index 1552.
def localCycle00061 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 5, .distance 4 6, .distance 1 6, .theta 1]
    constant := ![3, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 12 0, .triangle 34 2, .gapLower 6 2, .corridorLower 1 6]

-- Original cycle 140d630b5e2518fe3427bccfabde1fd1316768c71fe9b1a9623122ee79b8c3ab; original global index 1581.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 11 2, .gapLower 6 1, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 145816f482a42eb28b3e599556cb91542591be21d51c1e4bc8aec2663872d8f8; original global index 1605.
def localCycle00063 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 23 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 145d6d04df267934419adc9884323f322f67cfe5783821c9e7d4860c73eeb1f2; original global index 1609.
def localCycle00064 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .gapLower 6 4, .triangle 13 1, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 148178ae2a5f93cccc7777c37b5fa898eb960e04f8c8c506f04e740a58ea3095; original global index 1624.
def localCycle00065 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 18 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 14dfc8e7997005de97000383e8ada7a778405ef651c22639dd44f366d3d9cd7c; original global index 1655.
def localCycle00066 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 5, .theta 5]
    constant := ![3, 0, -1, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .gapLower 6 3, .gapLower 6 2, .triangle 4 1, .triangle 24 1, .gapLower 5 0]

-- Original cycle 14ea3a0c308a0644095108cbf708f09cb0b852be8eff988c50fc847bf7987079; original global index 1661.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0]
    constant := ![2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .gapLower 4 3, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0]

-- Original cycle 1502b6f81a146a760a7158f140ca4304b16ca63688b9653b7e47e9f3a1c4cbae; original global index 1666.
def localCycle00068 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 152b7bb92c3457edaa09604af42af818cc85e8e821c437a56f3fc5aee7a7a5b1; original global index 1676.
def localCycle00069 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 18 2, .gapLower 6 2, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 15b3a747d0d0be85ff1079afcd545fafc1caa946b09b2c385f11a1a0a609daef; original global index 1725.
def localCycle00070 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 4 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 32 1, .gapLower 6 3, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 162ffb6a18d302458d4057d7cf26045b2f3eeae484bc4eb48aa5eb55010b0472; original global index 1752.
def localCycle00071 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 28 0, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 16420727fde9801009558d494b45859374d9aca618547125b8e4afc781f10b92; original global index 1754.
def localCycle00072 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 5, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 2, .triangle 14 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 1679e0a235e329d71ec34267182f8ade1d6493c72ae0f19236648d0bdadd04df; original global index 1766.
def localCycle00073 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 4 6, .distance 2 4, .distance 2 3]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 29 0, .gapLower 2 3]

-- Original cycle 169d3f9f7b834ba66fe6be63f09801f2bbeb550c125524ef08e3661b566d7765; original global index 1772.
def localCycle00074 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 2, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 16a240a63c007920c486f6fee79f703fa7b226d6ee9bb47736364f65b1342651; original global index 1774.
def localCycle00075 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 3 5]
    constant := ![2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, true] }
  origin := ![.gapUpper 5 5, .triangle 34 2, .gapLower 6 4, .triangle 33 1]

-- Original cycle 16a561ef24375b0baa202b8f15de2e786ad125f69547d84fd4572eb628875572; original global index 1776.
def localCycle00076 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![4, -1, -1, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 28 0, .triangle 29 0, .gapLower 6 3, .gapLower 6 2, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 16aac7ef8548b87e930726b1628f68dd422c02bbdc017a3ed18a4491e8f84167; original global index 1778.
def localCycle00077 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 3, .theta 0, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, -1, 2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 1, -1, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 14 0, .gapLower 0 2, .corridorLower 0 3, .gapLower 0 6, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 16b672bf500bb1e32525db9c54653c432b2da6d7d2bd2a78cbaa30fb502fb246; original global index 1782.
def localCycle00078 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 6, .distance 0 5, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 14 2, .gapLower 0 3, .triangle 7 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 16c810eee9e0ef23ff286c37bdf8847f73dafe116eedccaaf6726c7ff8316f6f; original global index 1790.
def localCycle00079 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 177a2f705819c3079d5ac1791fbf76e686559dd49de7ce2fda31ba890b74d7e7; original global index 1838.
def localCycle00080 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 17ab62957c67ae53d192841db4f72e4b356503b831ee1bc1298f3d50d0907cd3; original global index 1850.
def localCycle00081 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, 0, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 27 2, .triangle 8 2, .gapLower 6 3, .triangle 23 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 17d5579bbd60659f2ec2107d5e095f6f6145d57abd6eeb09128707af07134653; original global index 1862.
def localCycle00082 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 8 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 1874005b9ab5c9f133ed6b58d2b6a89535d4d4741074b564da795405dbdd67da; original global index 1915.
def localCycle00083 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 3, .gapLower 6 3, .triangle 14 1]

-- Original cycle 18af0c03ce29a95db1d959c56053ef4f5c4776a0c86d16517104a0625c22f717; original global index 1930.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 2 1, .triangle 22 0, .corridorLower 4 5]

-- Original cycle 18cc650ba7bbd4f5eba0f3f82f265e4f1b2386f537d249ef21618efbda8cfdde; original global index 1938.
def localCycle00085 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 14 2, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 1937d0c7e4572664d03683dbe6dee4fe783f5042dfea54ed76953f79f82eedf1; original global index 1971.
def localCycle00086 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 12 0, .triangle 9 1, .triangle 5 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 1978b20d83a919a5b10ddc8eb2d853394342d3e9320403eba5664fbb66fd29c0; original global index 1988.
def localCycle00087 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 4 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 23 2, .gapLower 6 0]

-- Original cycle 19f8316d1e85979da81f2d71f1eaf6e4d0e3bb251ce971a900cfbae8c5a9d258; original global index 2027.
def localCycle00088 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .gapLower 6 3, .triangle 18 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 1acabda2eb756f8e0b3e566271fdc4fdf056afb09f8349b235c134c0d12e448d; original global index 2079.
def localCycle00089 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 4 5, .distance 0 4, .distance 0 6, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![4, -1, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .gapLower 6 2, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 1b3cd399bc7bf0596a3e49d8257b1a7bb0e1a0db3b3eca0b0e1382afda313ff5; original global index 2110.
def localCycle00090 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 0, .triangle 14 2, .gapLower 6 2, .triangle 23 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 1c178cf563e9911f7db4b991ccd8c5879fa39220b146e87ebbad57f8c2d13ecf; original global index 2168.
def localCycle00091 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 6 2, .triangle 12 0, .corridorLower 4 5]

-- Original cycle 1d06efaebd49b765f7c93e2857f11dbf752a7c2c91c5dd81cd79695db0319ac7; original global index 2237.
def localCycle00092 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 1d1a6b0763b76348aa9526cc29bf5c4738b3c7d06264e7cb1f0e19b85bb3f562; original global index 2240.
def localCycle00093 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 5 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 1dc748842ac4ff9df9aa09d5e88ffa0f01014314a8678efe774a90ac9a504b6c; original global index 2287.
def localCycle00094 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 12 0, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 1ebef74f54d80e4704238225b7f4ca1d52784a87b1e91c7640cf3caf200b25f0; original global index 2359.
def localCycle00095 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 0 2, .distance 1 2, .theta 1]
    constant := ![3, -1, 0, -2, -1, 3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 6 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 1 2]

-- Original cycle 1ec84ef5d46670f7d3c074fbf136fccd8250e2e4e5c0a3ca7049b1e5edbd4c8a; original global index 2363.
def localCycle00096 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 4 1, .gapUpper 1 5]

-- Original cycle 1f00633f9980f14d225fcd739776f76239704fe6cbbba22238edec74e33c1926; original global index 2379.
def localCycle00097 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 5, .distance 0 4, .distance 1 4, .theta 1]
    constant := ![3, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 4 2, .gapLower 0 4, .gapLower 0 3, .gapLower 4 1, .corridorLower 1 4]

-- Original cycle 1f35ddb562819c41d5c95585151c31e2275f966544f77b917d03611517577f1a; original global index 2395.
def localCycle00098 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 1f61dad1bb60f8ee2acb0492f89d19f85d1ebc7943b9d4ef9f54a3b88a6bb134; original global index 2406.
def localCycle00099 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 3, .corridorLower 4 6]

-- Original cycle 1fd2eb727c1739343e51868c0ba6b5117b60d54c5608351ac3ce6fb434db9b7f; original global index 2444.
def localCycle00100 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 13 1, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 1ff76212a1876723c9023dc29df86f284b34b080c92f748138b4dca35c4526f3; original global index 2452.
def localCycle00101 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 6, .distance 0 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 13 2, .gapLower 0 3, .triangle 6 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 20e27de3d6d69fa3558a531778f74a388f43564358b3a388f0384f4f8271baa1; original global index 2523.
def localCycle00102 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 30 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 214740365bbd99125a55b640ab30f0df281dfbb91996fc9ce37b42731c40b636; original global index 2550.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 21766cdd929a0fd5e316138034ef33dd4b3cbb6fde8573dc59f9ff67a7acdf21; original global index 2562.
def localCycle00104 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 1 6, .distance 1 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 1, .gapLower 6 1, .triangle 24 1]

-- Original cycle 217a0f61d52c3f896343f31e37cb1da1a7013a700049c8156dd517450dbf7de7; original global index 2563.
def localCycle00105 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 21abd3dd9e3cb0356ddd48477e7f81df3bf8c61e9a65f36717033cdfe515e9b7; original global index 2578.
def localCycle00106 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 5, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .gapLower 5 3, .gapLower 0 4, .triangle 4 1, .triangle 24 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 21bff1d75cdc5321172f0e336ed2ee2870d5a0932dfb4695d8c7a6c040cf2ad8; original global index 2588.
def localCycle00107 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 29 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 22996a966166603f989f71e6786f7820d2c5f5978b2d5cbb344710b5abc8f5c6; original global index 2646.
def localCycle00108 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![4, -1, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 31 0, .triangle 32 2, .triangle 27 2, .gapLower 6 4, .triangle 13 1, .triangle 23 0, .gapLower 4 0]

-- Original cycle 22d8be4aaa02611194458d743a60a2853b42f7098370163c924d0eb626060ea7; original global index 2667.
def localCycle00109 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 4 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 29 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 232ff4d68fbd31c046f3cea333529270b2f23d93052e39c642d49308605eb314; original global index 2700.
def localCycle00110 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, 0, -2, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 24558775fd931b53f56e0edb28e359e7234c3c76b981b2be05ba31e1e900174a; original global index 2786.
def localCycle00111 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 29 1, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 2482647074acc7062952be3814b7ce43d63f5d760bb8c290426256a190420c0e; original global index 2800.
def localCycle00112 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 0 2, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 0, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 24b729c9f9f3c7c6a8781a9aaf997024973c6c5c32c1bae66df012317a8557bc; original global index 2816.
def localCycle00113 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 30 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 24fd7b949a470e75de82d85b9fa5467d446c433282a6d8d49d4326d133109c22; original global index 2837.
def localCycle00114 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![4, -1, 0, -2, 0, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 29 1, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 2510898fd427a40745ae8cb3656629c6a3e50fc00e4c9e17ae67df863dd9244d; original global index 2848.
def localCycle00115 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 0, .triangle 28 0, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 2568a0724a433a74a9ab8c55445d4caa7bac4bfab8210f6507f6cf5c38d5061c; original global index 2878.
def localCycle00116 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 2599a86d7a075e0d205d5d4266519f382bfe14823b5d84385bbe1aa04a2520ef; original global index 2890.
def localCycle00117 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, 0, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle 25f3140bdb316097799c59d0715f6d93938a4c30e279ff2e9fd256d4d7899705; original global index 2911.
def localCycle00118 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 6, .distance 0 4]
    constant := ![2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, true] }
  origin := ![.gapUpper 4 2, .triangle 34 1, .gapLower 6 2, .triangle 13 1]

-- Original cycle 2627e21ba91d54345b7fd678422e5912197c33cad601c9d24d10ecf0ee5512c7; original global index 2923.
def localCycle00119 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 4 6, .distance 5 6, .distance 0 6, .distance 1 6, .distance 1 5, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 29 1, .triangle 34 1, .gapLower 6 2, .triangle 4 1, .triangle 24 1, .gapLower 5 0]

-- Original cycle 26e47f5c226ef369fb5e8e105f5a8dcce74d28163d96628f8ee3d0f833a51b58; original global index 2978.
def localCycle00120 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 4 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .triangle 23 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 27ba1aef88325d3cf92a7d0679904e29f4a668338167827d21453ec28d01ba2f; original global index 3033.
def localCycle00121 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 28320bf963acf88b9e67b2e412b1ce3b017c2fff66bb085c0f0b7e79c32e3269; original global index 3077.
def localCycle00122 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 6, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true] }
  origin := ![.triangle 2 2, .gapLower 0 4, .triangle 13 1, .triangle 23 2, .gapUpper 1 5]

-- Original cycle 283f4ebf03e18e6befe59a5147a914ea516da2b3bd39893bac786d29bfc50a25; original global index 3084.
def localCycle00123 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -3, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .gapLower 6 2, .triangle 13 1, .triangle 12 0, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 287ebcfa86ef467476633cb2a2193d4cc6a318dc2023126a9ba7e6f31ac0a3cd; original global index 3102.
def localCycle00124 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 3 5]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 33 1]

-- Original cycle 28a974669aa912301eeb1526659790d58d49f3b07c32e5e73fa3ae2f5417339b; original global index 3112.
def localCycle00125 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 23 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 2a10bd8f356d2757a13ae9d7da6d990ab1e88e0f0d490c7237c70c21471bd438; original global index 3208.
def localCycle00126 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 2a2df5531634bf32c192caf87ce0282534362d886ba57ad17edb8f10babab5cd; original global index 3214.
def localCycle00127 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 2a54aa2e7c49f4eb76f9f7e0ec941bac7f0fe5d7e2749cab39918557734a2931; original global index 3228.
def localCycle00128 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 2b40795f159cf349c9677d3b282300f35754de616f4ebfe43778a72e0b26fc65; original global index 3302.
def localCycle00129 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 2, .triangle 12 0, .triangle 34 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 2b5dd5079c7c4c0b3e7a1037ac3ea6f26982cc99122b559685a8e19810148e43; original global index 3316.
def localCycle00130 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 4 6, .distance 1 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 23 2, .gapLower 6 2, .gapUpper 4 1]

-- Original cycle 2bab5f0d89154e7e388124f86058f5be76e578d8441e4d1286b82be46f37ff83; original global index 3338.
def localCycle00131 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 2bd1c648861179db09d52db70f10b0617d801ac11c12892f74dd525921b5e8d7; original global index 3354.
def localCycle00132 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 2bdbe2765c51e7efdf8869aff44eb05c61b98d4276b08c5dd677bc6334a7669b; original global index 3356.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 29 1, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 2c12536a5a01d938f0190ac46ac580797d20b74f8ccf3502a90e3ffb1a3f5477; original global index 3371.
def localCycle00134 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 2d3fc4530e2201afcc31dde8026bdcb31dfdecae6c33f1330fbe31f66da6e645; original global index 3454.
def localCycle00135 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 13 2, .gapLower 6 2, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaNext 0, .thetaLower 0]

-- Original cycle 2d942570c5ab7b6d73c630b81823f53d7363c69367e200d6e27b161c5984543d; original global index 3472.
def localCycle00136 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 5 2, .triangle 14 2, .gapLower 0 4]

-- Original cycle 2db144d0b517f305211c3de791011fa5f0c5485cda2304cf6d06db678d68d7dc; original global index 3488.
def localCycle00137 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 2, .triangle 12 0, .triangle 22 2, .triangle 24 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 2db4df8a8371556192dcf2d8fbf6dc6b54773c748f368564a9c2b87537f90f8d; original global index 3491.
def localCycle00138 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -1, 0, -2, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true] }
  origin := ![.triangle 3 2, .triangle 12 1, .triangle 13 0, .triangle 34 1, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle 2e2a5ddbe4edfab7660488e53163b038e3a14d16b02e7b2fb3ba2dc6e9ec7764; original global index 3529.
def localCycle00139 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 0, .gapLower 6 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 2eb2351c2a00faab8226688e3d68f26527e4121da12e2563c46d5e0410939417; original global index 3573.
def localCycle00140 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 1 6, .theta 1]
    constant := ![3, 0, 0, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 12 2, .triangle 14 0, .gapLower 6 2, .corridorLower 1 6]

-- Original cycle 2f1dcc438eda6b87d5672fa69c22bd29ebdb0f9fd1892b3104272958c12232d8; original global index 3601.
def localCycle00141 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 11 0, .triangle 5 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 2f21ff58d33f74a8ae10865437877b9d406b02a56bc91f2c39d54eff91543ab3; original global index 3604.
def localCycle00142 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .triangle 8 2, .gapLower 6 2, .triangle 23 1, .gapLower 6 0]

-- Original cycle 2f69651f9b3e16fbba046a45f4bb9233acf1aa62efb6264cc4d305efc6a53015; original global index 3625.
def localCycle00143 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 300d8e9e1643621a77a7fffc049e8a2c8761d7adef31352983e55fbfa4703f99; original global index 3662.
def localCycle00144 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 30406780557f7d32cb80e076280f7ef8fb6cbb40ac2c37e8f191ea50d3c686a4; original global index 3672.
def localCycle00145 : Cycle where
  length := 3
  data := {
    node := ![.theta 0, .distance 0 1, .theta 1, .theta 0]
    constant := ![1, -2, 0]
    coefficient := ![1, -1, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 6, .gapUpper 1 6, .thetaNext 0]

-- Original cycle 304301f493f3674b72c3e2162df5835a0ce78393af680d3f1cf34a7ede376603; original global index 3674.
def localCycle00146 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 310ebd0cda51800afec09a9f56edc7432e26fce029dc1fb13415ef738901eec7; original global index 3738.
def localCycle00147 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaLower 1]

-- Original cycle 31885c9d1124f033d9d79b67ab4eaffafce3871732ec64f0b25497b15fc9be96; original global index 3777.
def localCycle00148 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 0 5, .distance 0 4]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 4 2, .gapLower 5 2, .gapLower 0 3]

-- Original cycle 3192a7dac4ba315cdf07204b2e2f24d7f72849c2284cf717760cd91523b26b93; original global index 3784.
def localCycle00149 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 25 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 319fffc1c287d8f7408fd362af23c5910e5fcfc716b08c0ef65db1f6dd56b9ad; original global index 3790.
def localCycle00150 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![-2, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 5, .gapLower 0 4, .gapLower 5 3, .triangle 22 2, .gapUpper 1 5]

-- Original cycle 324aef30a3b4c9b1a30935348545ff4403f0b56f840ccf6e953cec91fd9c7c4a; original global index 3841.
def localCycle00151 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 18 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 328cfcd4dcce8cdf23ed9c0305cc04c85bbe35a9fe31ae980107bc4833ba43b0; original global index 3867.
def localCycle00152 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 6, .distance 0 5, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, 0, -2, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .gapLower 0 4, .gapLower 0 3, .gapLower 5 2, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3]

-- Original cycle 32c0ed177b60dd9552575b0a46d8b1e8daa4c29d5ed93798d3740d6d992d271d; original global index 3886.
def localCycle00153 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .theta 1]
    constant := ![3, -1, -2, 3, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 27 2, .gapUpper 2 6, .thetaNext 1]

-- Original cycle 334c1ae8746b1121178556eea20ef6b5e3c0e0e7591de01e6d7c116fe285b16f; original global index 3925.
def localCycle00154 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 13 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 334e87121add7982ba07fb8cc0bc9ea206a32ff40567dee7553c407955b2d09f; original global index 3927.
def localCycle00155 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, -1, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 3376642a96131b9eeacd645104478b0d06b24e6cd9a6624bcaf042eb97c0c52d; original global index 3937.
def localCycle00156 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 33904cae8605b0e8b7309e8be1dbcf0086fad1bee3ebaa326dafd4093a082b24; original global index 3945.
def localCycle00157 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 342ad4ed83e9e37129f35af26290356fa8aa5b01671d0f5e5379ab98d8bb670e; original global index 3999.
def localCycle00158 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .gapLower 6 4, .triangle 18 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 34e80258ad9c4df80b83785bd7d5eb807ad86656a30919811eddf592ec7b341c; original global index 4047.
def localCycle00159 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, 0, 0, 0, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .gapLower 6 2, .triangle 13 1, .triangle 12 0, .triangle 22 0, .triangle 19 1, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 350f3c3e29f1af4612e53cc0dca1af66c83560124a725fa2247c71e299dcb7ae; original global index 4058.
def localCycle00160 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 5, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .gapLower 5 3, .gapLower 0 4, .triangle 14 1, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 35123bd7a5c4f587570e401b7f707372c5073bf8e3dfa8ef4977b866b12a8ddf; original global index 4059.
def localCycle00161 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Original cycle 355215998e4ea2cd8f81be5fe2a6bf8b8b695e2ae5534637a4458b548e67535d; original global index 4082.
def localCycle00162 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 6, .distance 0 5, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, 0, 0, -3, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 2, .gapLower 0 3, .gapLower 5 2, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3]

-- Original cycle 35574ce519b0a1ea69615a3aca089042b47af89843c7e8f949d63dc879844826; original global index 4086.
def localCycle00163 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 4 2, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle 358e0fef379ababdc8a4283d6e0c033589e86e21f203e9d06e74d82ca32f3ffa; original global index 4102.
def localCycle00164 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .theta 6, .theta 5, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, -1, -1, -2, 0, 0, 3, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 26 1, .triangle 15 0, .corridorLower 1 2]

-- Original cycle 366dbe5aacd53f78300f7ee4e1ee2d9d25905c56f8e5029ec12fda7dda62e594; original global index 4179.
def localCycle00165 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 14 0, .gapLower 0 2, .triangle 5 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 369ae7234b771b87ae8648e96c5f8e5def09737f29e178f8abe756737d6b3519; original global index 4195.
def localCycle00166 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 4, .distance 0 5, .distance 5 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -1, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 24 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 37350f75d31be93342d98404f31501f32968c3fdf30d95fb32525143b990aa64; original global index 4238.
def localCycle00167 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 4 2, .triangle 34 1, .gapLower 5 2, .gapLower 0 3]

-- Original cycle 374a92ab5d85ea718263f857a5d7b70235dbab4944c394976df5cf3aedb67702; original global index 4248.
def localCycle00168 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 5 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, -2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 30 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 37c4f03bcfaa1231d1a75304b571a919ac0e96addc7bb7c2dbd86d0db10b9b90; original global index 4288.
def localCycle00169 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .corridorLower 5 6]

-- Original cycle 37ead186e57fba4317dbf6c6550df3f633f9ab9a02d17b6796c3cada559f6ad0; original global index 4298.
def localCycle00170 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -2, -2, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .gapLower 0 4, .gapLower 0 3, .triangle 13 1, .triangle 23 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2]

-- Original cycle 37f5b2cf4365e9d1c6f4294072145868360c76c3f777120db5b76bf6c809b3cf; original global index 4299.
def localCycle00171 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 380a581c8e530b417bbdcbaf07dc363fa4509c6884555e30d253f2eecc8a5704; original global index 4301.
def localCycle00172 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .gapLower 6 3, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 38bc0a8f9abd5845ec5317bcf74e720015cb051a8bbb2d944a5c5171431fc041; original global index 4365.
def localCycle00173 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 38ce2ec3d7d0d360634a5e0f14aba6c4c6e7c7803c7e60de041d1bfb4c4c0e23; original global index 4372.
def localCycle00174 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 391ecff33b6a160344fe79f7ae17fcd2122076cab2a8b98659bf2b367d9eb3b6; original global index 4395.
def localCycle00175 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 3943ddeaaa72045b2642235b1e97f3040e57b7c1c4278c8015136cd52037c3ce; original global index 4405.
def localCycle00176 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 4, .distance 0 3]
    constant := ![2, 0, 0, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, true, false] }
  origin := ![.gapUpper 3 2, .triangle 11 2, .triangle 13 1, .gapLower 0 2]

-- Original cycle 394b9f378239d661df38cc1e095af2065479fbe4785a37194743c516d751c52d; original global index 4408.
def localCycle00177 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6, .theta 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -2, 2, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 2, .gapLower 6 0, .gapLower 6 6, .triangle 32 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2]

-- Original cycle 3aa74bebba2226da5ba47c970053821e24bfe38832c12e8a575ae9b40789ca1c; original global index 4527.
def localCycle00178 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 3ab5a9218319c3c3851b047c984a6f9a039fe443a203eb0cf8913cfb657ea26e; original global index 4531.
def localCycle00179 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 11 2, .gapLower 6 3, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0, .thetaLower 0]

-- Original cycle 3b9a922c34e93b43374b507fa83bce3bbbf684931c56ff0c713395d108168766; original global index 4605.
def localCycle00180 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 27 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 3ba86a5e3ef128e450c80f359a195989a22e90b2ad087b14587c7d9b6d19c364; original global index 4613.
def localCycle00181 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 4, .distance 0 3]
    constant := ![2, 0, -2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 3 2, .triangle 11 2, .gapLower 0 3, .gapLower 0 2]

-- Original cycle 3be91ba30c1f61f94a8f046c07bcb9d285e2e9ccc6af3954f11d6d9fb5797918; original global index 4643.
def localCycle00182 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![4, -1, -1, -3, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 28 0, .triangle 29 0, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 3c652b342b4468858b83f6d89198f56cecc2b3fa7ed3a9886bc7ddc53e50243d; original global index 4682.
def localCycle00183 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 14 1, .triangle 24 2, .triangle 23 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 3d885d83496ba8dc96d17591c88a884128de737d3b46ebe8700fdb0ad10ddc75; original global index 4763.
def localCycle00184 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 14 0, .gapLower 0 2, .triangle 5 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 3d93ac90057f6c0f8bfb0725d45b5410e6ac949eac5d595b019cc977928d7858; original global index 4767.
def localCycle00185 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 8 2, .gapLower 6 1, .gapLower 6 0]

-- Original cycle 3dbc14ba1c5235fb5e709fd4ca875e2635eb610d9ede0ff0c8ea68c0d47be721; original global index 4781.
def localCycle00186 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -1, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 3dc55e1dcd3f1f2b9316350e702e64a65f7953465e3260943991d81e955c1af1; original global index 4782.
def localCycle00187 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 3e0da6107b96c236d21afe372228e0025aa1784860324afdb48867d82d559778; original global index 4798.
def localCycle00188 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .gapLower 6 4, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 3e1e7a19f14c18df45bf544d451f68a6168cd4657aca2fda0f80831848ccd474; original global index 4805.
def localCycle00189 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 3e85a24a66501f16690d4d37242f21b111e7f8268c0c2af82dc81e5d732083eb; original global index 4836.
def localCycle00190 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 5 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 14 2, .gapLower 6 1, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 3f837ab44bc09f0b96ab6f93717cdabf76c9ccbaa0d1a15ab1c4747551e2520e; original global index 4908.
def localCycle00191 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 4 6]

-- Original cycle 3fc4df47408372851dc5aff192c0e4bba10372dbc14b2cda6935effb78298686; original global index 4925.
def localCycle00192 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 3, .triangle 13 1, .triangle 34 1, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 4011f3635b316721931f83830b372fa6862bdd789cdb175245579ac03b14c3e1; original global index 4941.
def localCycle00193 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 405bea06377b439baa1d1c78ea729f42577939984f1570448af74b2c2a7ab0fe; original global index 4974.
def localCycle00194 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 6, .distance 0 4]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 2, .gapLower 6 3, .gapLower 6 2, .triangle 13 1]

-- Original cycle 40adc4d66215babbb321ba94a49028ef4a8bc2ed0394bf0ae0bbe6ee5935545a; original global index 4998.
def localCycle00195 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 5 3, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 40f3c75198b191dcf498c8137dd0c0ee69c4f826a442c4f698029b0f2973c613; original global index 5015.
def localCycle00196 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 5 6]

-- Original cycle 414153474e981a6595e71eb33ac0c2ead3ffaa3d1cd7efd890b1b65ea4e471dd; original global index 5038.
def localCycle00197 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 5 6, .distance 0 6, .distance 1 6, .distance 1 4, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 30 1, .gapLower 6 2, .triangle 4 1, .triangle 23 1, .gapLower 4 0]

-- Original cycle 414627f7e1375c43a0e1edd1005a64a97c202981972d7cc8bc412562b655c486; original global index 5042.
def localCycle00198 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 2, .triangle 30 0, .triangle 24 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 41a70295efc19a1cb6dd986b335ba5587b4bae27f3bad0f8699ef42034b4d77b; original global index 5063.
def localCycle00199 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 4, .theta 4]
    constant := ![3, -1, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .triangle 8 2, .gapLower 6 1, .triangle 23 1, .gapLower 4 0]

-- Original cycle 41ffb90561b23f97d5049094496907fbc341b0018fdd28365ce9a09921a48df6; original global index 5085.
def localCycle00200 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 4 6, .distance 3 6, .distance 0 6, .distance 1 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![4, -2, 0, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 4 6, .gapLower 6 4, .triangle 11 2, .gapLower 6 1, .triangle 23 1, .triangle 22 0, .corridorLower 4 5]

-- Original cycle 43796b64c3f57b318bd34bf6577df94ef967c351053ce21b3a1f3aa443647dd1; original global index 5210.
def localCycle00201 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .gapLower 6 3, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 43818954b56c091647c07c96aad8ebd44c1eba38482b834e9157064e5d8f8e26; original global index 5215.
def localCycle00202 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .gapLower 6 3, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 43d8b05f2b2a9080cd4316ee7da8ecb91ce49f978077ebcb6fe118e49bfaf734; original global index 5250.
def localCycle00203 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -1, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 43f0851fe5fb0adde606a991bdcabeef5c12e8d2c556a57356b8ece8df198bf4; original global index 5257.
def localCycle00204 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 23 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 43f1576b0e03684289ae692cf3066fb58241b1ae7845aba0a12f35957ca0d4b5; original global index 5258.
def localCycle00205 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 44333d968afbca3c77b7124724a93040f00b8eb98093e941c7cfcde87ad84f5f; original global index 5278.
def localCycle00206 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, 0, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, true, true, true, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 14 2, .gapLower 6 1, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 44909177a68273caa9ff53c8753564e9265dcb6d92c47d14ae26327eaafdc8ba; original global index 5307.
def localCycle00207 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 13 1, .triangle 23 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 44ad01dcfacfe6f75d7924dc6006e090bd0d7756265e07355168167681112bb4; original global index 5321.
def localCycle00208 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 4505dc51cffed38082bdf028e0a28bb92bf1e8fc81789d6abe6c25ce68863c05; original global index 5341.
def localCycle00209 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 23 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 452a47ad1eaed52a29541673c9edd208a3a137a7ea83002d4d835e7f1df390ac; original global index 5350.
def localCycle00210 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 45503e2154530a293d5173c435abadedad1345b0842bdb2a24e533f6c9b82dcc; original global index 5365.
def localCycle00211 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 4 1, .gapLower 6 2, .triangle 24 0, .gapLower 1 3]

-- Original cycle 45857f3edca7eae5c2d74c85de5ade10ac8d9472c7f739e663e4a3dc689ebe1f; original global index 5377.
def localCycle00212 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 6, .distance 0 5, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, -2, 0, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .triangle 13 2, .gapLower 0 3, .gapLower 5 2, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3]

-- Original cycle 470a6f30739d0504982904562240b005c6a57d5cc7f8d7e8eff6d71321a4f7f3; original global index 5507.
def localCycle00213 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 13 0, .triangle 12 0, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 471bea08cc2880980fb2b142a6c76210dc270fa10e680209554e6020a277f9df; original global index 5513.
def localCycle00214 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![-3, 0, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 5, .gapLower 4 3, .gapLower 5 2, .gapUpper 1 5]

-- Original cycle 47219a1a9c35dc3ff926ca2c2dd1d9c696b73dcb9f097c9c37221c4c8c03e57f; original global index 5516.
def localCycle00215 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 6 2, .triangle 12 0, .corridorLower 4 5]

-- Original cycle 4769a71979fba2376239d7670be914cd32986f4474843b2b6b0b5f8398bd31c0; original global index 5530.
def localCycle00216 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 47bb8663153d2d0bff301b3a5f5fa59c92767f256e0254918f2e75a206c32ab7; original global index 5556.
def localCycle00217 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 8 2, .triangle 13 1, .triangle 23 0, .gapLower 4 0]

-- Original cycle 47e63af137abb02664f8eef46adf0c3da8312cd82df5e3335b552af3df971929; original global index 5565.
def localCycle00218 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .gapLower 5 2, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 485612164ff286b7bc24d45ff29bfca68287565da5a4ed921e2a8a5b8546ea3c; original global index 5601.
def localCycle00219 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .triangle 23 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 48cd189e52d68fa08a8866d6d090b4a69dbc3da97fe606b2659e7f149ce43c3a; original global index 5639.
def localCycle00220 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 2, .gapLower 6 5, .triangle 8 2, .triangle 14 1, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 48dacef03e0a312b0071d6fad103de1169333bc8e66b70d169ccbaa17c38d462; original global index 5645.
def localCycle00221 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 4 6, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -2, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Original cycle 48fc73cc27e66bad4cde77b320fc62cfe32a7e0d21a5c8a8ef35b7f1fc87676b; original global index 5651.
def localCycle00222 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 2, .gapLower 6 5, .triangle 8 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 491e1be6a29c8f46139e8f952bd9a1d1262d57a78edbeab8681c8a850dd5ba03; original global index 5662.
def localCycle00223 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 14 0, .triangle 7 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 495972ce042b2170151a6768d433dd52a580292fb2433923d273ecf0d3d1b529; original global index 5684.
def localCycle00224 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 4, .theta 4]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .gapLower 6 3, .gapLower 6 2, .triangle 23 1, .gapLower 4 0]

-- Original cycle 49e7f54a953859dbc7b2528f04fd883a1a1ddbb6598be0246bf4d82acea6a2f9; original global index 5734.
def localCycle00225 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, 0, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle 4b576ff9fc6d69c7fa9a949d3de01defcae34c7d8e0385b20ffeb2c3b215f924; original global index 5837.
def localCycle00226 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 8 2, .triangle 14 1, .triangle 24 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 4b859f6dec0948eec8c495740579f69f1fdce8ed3ff3a5046c052958ddb86f77; original global index 5858.
def localCycle00227 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 13 0, .triangle 6 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 4be708d78752928b2e859696a1ed313907adedecd35c458d0b20852c25643657; original global index 5895.
def localCycle00228 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 4c5651e8a2db6f1a1cbe8167b11fcbb92b686e7656790c20d715c52c93a8f5e7; original global index 5925.
def localCycle00229 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 2, .gapLower 0 3, .triangle 6 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 4cff97bd25058f5824c644b5dbd38868122d5e5b507d01d2a83a6bacdb8243ee; original global index 5981.
def localCycle00230 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 0 5, .triangle 13 0, .triangle 23 2, .gapUpper 1 5]

-- Original cycle 4d7828c54237bd41847d02374b1ba79f48b2c1642960ec02a3a6cba4eba48cc4; original global index 6014.
def localCycle00231 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Original cycle 4dc5c44f326096902f67dde0a0f9d56b3e6dfbfd638100ff77c503e34f42dead; original global index 6038.
def localCycle00232 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .triangle 8 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 4e03c05da525bcbadf6084aa2fae1043500af0475853893a2aa558883c6ea410; original global index 6057.
def localCycle00233 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 4e6002eccc2931150c8bacd3ba79a774f2a8980f455f18b32b538a056410dc40; original global index 6086.
def localCycle00234 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 4, .distance 0 5, .distance 5 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 2, .triangle 12 2, .triangle 14 0, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 4e681af0a7f409b037dff311c4eaec6cad961de9865986f14c943c6701cc676f; original global index 6088.
def localCycle00235 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 23 0, .gapLower 4 0]

-- Original cycle 4eaa9b513809b85b94e81d0c68f84e6caaf12587c7f75ce80545b6c1a2ba8d43; original global index 6110.
def localCycle00236 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 4f2981d04455a5821266514525cf5378ac116010414fb4d4e248d6e04dc5c23d; original global index 6151.
def localCycle00237 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, -1, -1, -1, -1, 0, 3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 22 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 4f5b875a1284a609c3f4a3b8b555f849c49838b343d3a38cef56adc625199839; original global index 6168.
def localCycle00238 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 0 6, .distance 0 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 2, .gapLower 6 3, .triangle 13 1]

-- Original cycle 4f63ca6cbed472ae623ef3e8eb4bd3299cf117b0a934d9cf47b727ce6d1b32b2; original global index 6171.
def localCycle00239 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 13 2, .triangle 14 1, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 4f955f21f84f79b71ad3537178b2c15aa74cf1dd1ab394938126ff427356e995; original global index 6180.
def localCycle00240 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3]
    constant := ![2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false] }
  origin := ![.gapUpper 3 1, .triangle 33 1, .triangle 34 0, .triangle 22 0, .gapLower 1 2]

-- Original cycle 4fb34eeadd552adc589fa7675091b65d6364260d629e51a6d347cd5708332068; original global index 6189.
def localCycle00241 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 4fb6edf5c20d2771e5c0fe364d38c83cce9d0976bdae39be84d58a6110455a75; original global index 6190.
def localCycle00242 : Cycle where
  length := 3
  data := {
    node := ![.theta 5, .distance 5 6, .theta 6, .theta 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 0, .gapLower 6 0, .thetaNext 5]

-- Original cycle 4ff183a4951005fca814222b66a967e466c596d82d20848c94807efc85464553; original global index 6207.
def localCycle00243 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 502a6213e24cfc3ca87114bf4722e03d67d71c3e69f95dd401c8966cdd16f1f7; original global index 6221.
def localCycle00244 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 13 1, .triangle 23 0, .gapLower 4 0]

-- Original cycle 503ab277fbb955b984095eac604957e68a7d7aebbe543947f2a826f845a1c927; original global index 6227.
def localCycle00245 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 6, .distance 0 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -2, -2, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .gapLower 0 4, .gapLower 0 3, .gapLower 5 2, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2]

-- Original cycle 50711a628f7cb3e543c117441d1216d4249f77dbf912db667ddfdbfe7ff03f30; original global index 6246.
def localCycle00246 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 5181cd31931987ec299b38248aa7329924ef67c918f0c2aefbeadc1e058e56e5; original global index 6341.
def localCycle00247 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 25 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 5192cb175f57ce66619436ee415c26f63d7e22ecab7449cd2234d88d6bc23c97; original global index 6347.
def localCycle00248 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, -1, -1, -3, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 33 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2]

-- Original cycle 51add41b4e37203ed8fe3841b1d0df36a432e9f0a7a2ba9421f988785aa2e081; original global index 6358.
def localCycle00249 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 4 6, .distance 2 4, .distance 2 3]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 29 0, .gapLower 2 3]

-- Original cycle 52d28bc571c8ae6f706bc981daaa1a618bb14bc85782b2c66fbfde75738a0790; original global index 6447.
def localCycle00250 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .gapLower 6 2, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 53e26d8defe00418d1acdbf0323849f5332bb1741e02557c7ddc42e641d03abb; original global index 6508.
def localCycle00251 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 2 4, .distance 2 6, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![4, -1, 0, -2, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 547c7b8033c39a29805ef3ad99cf6e316e1deb54fa3e49546d121cce1db3a8ef; original global index 6546.
def localCycle00252 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 0, .triangle 28 0, .triangle 25 1, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 547ee7d71a62cabe1f0060786cff8c352d865a4a47a5acbc29a59b0e74360147; original global index 6547.
def localCycle00253 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 11 2, .triangle 14 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 550c276925058888a8d53df36016989d4793f79dc6a33dcb0949c3423ff0a1b3; original global index 6587.
def localCycle00254 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 553e34b80fa6cfc0f755944c7d1ed113654d2c963e59c708a8bf67d828f91c3c; original global index 6599.
def localCycle00255 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 13 2, .gapLower 6 2, .gapUpper 4 3]

-- Original cycle 55af537e33766f46ded17f442b8392ba3532c5b0231cf2e8d1084c6041843df0; original global index 6647.
def localCycle00256 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 13 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 55b8490fee565f0bae9e300bb8a871abdf6b0873510e6ed0e9b7451f0a51044d; original global index 6648.
def localCycle00257 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 5654a0e7b6143a185892db9099cfbd799bfebb39802ec5a0735a7c383ac446b9; original global index 6692.
def localCycle00258 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 2, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 568b64c94cc95c9dd53cdb7e12f1e6f49e400420471e7a1feb5b540d477bad0a; original global index 6710.
def localCycle00259 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .gapLower 6 2, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 56d704f94cda1976db1b9f5c180a4d5037c59d51e7047f5db543c7625147f220; original global index 6735.
def localCycle00260 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 6, .distance 0 5, .theta 0, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, 0, 0, -2, -1, 2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]
    strict := ![false, false, false, false, true, true, true, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 14 2, .gapLower 0 4, .corridorLower 0 5, .gapLower 0 6, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 56d95f905f6c47388b66defdf324f28058efea3b1802e26e9d902170a91a8898; original global index 6736.
def localCycle00261 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 3, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 575915fcc592857fbae4d3b486be2c5bc3d01958cfde71dbd747e5480be9b289; original global index 6772.
def localCycle00262 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 576c2f0d6b7347893f8e78b445af02faa3895fca1d68ef50500d4cb6343eec91; original global index 6779.
def localCycle00263 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 1, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 57f99f117e47b113aaa763d9669b5044c773f60f59bb086087c1bd8411d90b23; original global index 6827.
def localCycle00264 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 4, .distance 4 6, .distance 5 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, true, true, true, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 14 2, .gapLower 6 1, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 591102f3f67aaaba4da1d31e03e0b07fe27f6de693b625c3fdd4ae55f1f02ab7; original global index 6906.
def localCycle00265 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 14 0, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 591c8cd434afac5029b0d8cd043fc4fa1f501c67d0d93f46e0f0fdc29df9abc7; original global index 6910.
def localCycle00266 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 13 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 594ae0e555780a01e291858e7ef5fd545adc4f53db1c491dff96164731da423d; original global index 6928.
def localCycle00267 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 594b825d0b0985a90ea04582868cdd9449786b881a6b35d2be6ebf60898d6fc0; original global index 6930.
def localCycle00268 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 2 6, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 4, .gapLower 6 4, .triangle 30 1]

-- Original cycle 594c9b6ea8250ad7d28ce3b7a950d249b80dc6e9300bd8b281d28f103f52d379; original global index 6933.
def localCycle00269 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .gapLower 4 2, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 597136bdec5fa5bd7960f2813914e99a6e97219018de315cf63886160ccb9b8e; original global index 6948.
def localCycle00270 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 59e0d6317bdb989a12683a1e7fde4aa0d830fed07c7d643559a4e9dfa3c9fa1a; original global index 6991.
def localCycle00271 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 59eb58f70b56a8ebb4e1a0394da586ff8302bf06a0a4be2d6170a6a012d8773d; original global index 6997.
def localCycle00272 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 4, .distance 0 6, .distance 0 5, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0]
    constant := ![2, 0, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.gapLower 0 6, .triangle 2 2, .triangle 13 2, .gapLower 0 3, .gapLower 5 2, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0]

-- Original cycle 5b54fb8247f86a6c15058a27068c85381c6433432cc546aad0dad959e1f6537e; original global index 7108.
def localCycle00273 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 5b74ce6a221e8213be535a074dbb0380d1c320c24658b21669e47d8b69a26d30; original global index 7116.
def localCycle00274 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .gapLower 6 3, .triangle 14 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5bfc772a998e66f4760d1c5e9a187180448f476e3ca8463f84790cacfc306245; original global index 7158.
def localCycle00275 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![4, 0, 0, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 15 2, .triangle 19 0, .triangle 25 0, .triangle 26 0, .corridorLower 3 5]

-- Original cycle 5c1b664ff0257f37dcfdd7dcdfa078dcc19714951215782477f930c13963dbe1; original global index 7170.
def localCycle00276 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .gapLower 6 2, .gapLower 6 1, .triangle 23 1, .gapLower 4 0]

-- Original cycle 5c3ecec023570ace9d4fcd7651d844cef3148c3450d8dbe99a0ceda6460f1154; original global index 7182.
def localCycle00277 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 2, .gapLower 6 2, .triangle 14 1]

-- Original cycle 5c7db325de14118b1f3920719bef322a6f47d967b44bec125d1074659195cda7; original global index 7201.
def localCycle00278 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 27 2, .triangle 8 2, .gapLower 6 3, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0, .thetaLower 0]

-- Original cycle 5ca55dde7526f11f82730483875c03b6b51b0aebd2e226c2ee19ba22f6f1038e; original global index 7210.
def localCycle00279 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .triangle 8 2, .gapLower 6 3, .triangle 23 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 5cd61694f127c91fed896dec404671b9d1eeba015dbeff17de906b69cd8da802; original global index 7225.
def localCycle00280 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5cdc2d3d448984eb9ac15fe9d563732f8c48d91e69119963517061099556877f; original global index 7227.
def localCycle00281 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 4, .distance 0 5, .distance 5 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -1, 0, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 24 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 5d420ef563db529be810ab1c9aeb17e2e40df1eb6f718ab7d3f13644ce3db135; original global index 7259.
def localCycle00282 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .gapLower 6 3, .triangle 14 1, .triangle 24 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 5d55893ad11fd6ee90f150addba03e059bd1cb7b93d236bad4fe70bd87d46365; original global index 7264.
def localCycle00283 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 5def76a34e6396646987530e65e26b08522c0f4a8aa9a5ad9cfda447b0899e5a; original global index 7306.
def localCycle00284 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, -1, 0, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 5dff7e70a40eefc34eeb38c99f5b5500638c23491d23e8328d77fa0d0eb69125; original global index 7310.
def localCycle00285 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 2 6, .distance 4 6, .distance 2 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 29 2, .gapLower 6 4, .gapUpper 4 3]

-- Original cycle 5e1380ce33fc16cd7b5a4dd3e59c1a4318c82fd9029da6d183c6d4f60c63fc93; original global index 7316.
def localCycle00286 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 1 6, .distance 1 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 2, .gapLower 6 2, .triangle 24 1]

-- Original cycle 5e893545b2ac81606bd51082d6d16ed49573b4a6b479ef42fc1596999237d85d; original global index 7353.
def localCycle00287 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 0 6, .distance 0 5, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -2, 0, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.gapUpper 2 2, .triangle 8 2, .gapLower 0 4, .triangle 10 1, .gapLower 0 1]

-- Original cycle 5eb647b6117319dffee761454f86191271bf55ec9cec3d2760e9ef78b6d49ad6; original global index 7370.
def localCycle00288 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 5eec70e62d574e7e733c932899598d2e351d7dddd7b112ba5d3de222bdce25ad; original global index 7389.
def localCycle00289 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Original cycle 5f6fb676dd450c3d5b9c41efb54427ee36158791ccc3e6bda631b3319012f102; original global index 7432.
def localCycle00290 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, -1, -1, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle 5fb7245df6da0bad9d1eaf1d9da1128d94773243271bd8aa18346a4e57e7eb58; original global index 7454.
def localCycle00291 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, -2, 0, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, true, true, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .gapLower 6 2, .gapLower 6 1, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 5fd2b88e7f5748654380fe7aba625eea3b18d002fc3346cf68dcad91d3aca933; original global index 7471.
def localCycle00292 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 602d757a0e4e68e7cef3e8a2f04ce04498f1e7659de7efe08438ea68e75871c7; original global index 7494.
def localCycle00293 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 14 1, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 604e72c879c44083a70821b534a41442f125fd6e74952fe4f329e72bf2714b1e; original global index 7499.
def localCycle00294 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, 0, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 13 1, .triangle 23 0, .gapLower 4 0]

-- Original cycle 60bed6256c79f75d2c3404c8a72dc27ed045ee2b736ce1d429391d8b319f56db; original global index 7534.
def localCycle00295 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 60dd6e93859b0a75dbd46d25cfd76c634b09599e394ded73cd97bb863c476fad; original global index 7548.
def localCycle00296 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, 0, -2, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 27 2, .triangle 8 2, .gapLower 6 3, .triangle 23 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 615a148bac1e55e9d1253135ff9ec99c87f8543eac28ed69570286d3b9db4bca; original global index 7591.
def localCycle00297 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 61ace397a2b4e1d411bc13f4f4fcaf479c03c67a64e10aa18d639f339e084a05; original global index 7621.
def localCycle00298 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .gapLower 6 4, .triangle 13 2, .triangle 14 1, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 61f76144fe53aef1ebadec546a85fbde9084ca2ff776588dd4a33cc4ee15a659; original global index 7650.
def localCycle00299 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 626011331b0e8c60dc3d6522fc68d2dd0d2a35de54e767008352b398f4e486a0; original global index 7679.
def localCycle00300 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 2, .triangle 12 0, .triangle 22 2, .triangle 24 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 62813c47ce70505a25184a8d12407fbe5f242e27394ee1d7879dea2e1a26ee34; original global index 7686.
def localCycle00301 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .gapLower 6 3, .triangle 23 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 62910ff18385d3ffa206da262ee8b2db0a6d42f05cbfe54b0ffebfb12b3f6857; original global index 7691.
def localCycle00302 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 27 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 62deee0c598a69d190a037ff4185e498e7e3a5900f2cb877f965ed08b8e010dc; original global index 7715.
def localCycle00303 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 8 2, .triangle 13 1, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 630ab04fa1eb95a6e1a29d4070b8f73af7fdbe4ae579028c89494638b52c2222; original global index 7720.
def localCycle00304 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 2, .gapLower 6 3, .triangle 14 0, .triangle 12 1]

-- Original cycle 6311e3c4c9051bffa6cdcc368301edbcedbbdd4783ae16c8f622b3bb7b1ef095; original global index 7724.
def localCycle00305 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 63885fd5b9f32b378627b95221ee7b7218c4cd4691eaad89271a8d18acef7c48; original global index 7764.
def localCycle00306 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 23 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 63ccae85c2513ab4cadac12307b664356e4c8efdf03d7fead0a1aeb1829638df; original global index 7778.
def localCycle00307 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .gapLower 6 3, .triangle 23 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 64aef6dc757a70f1c954d9ce83b3434f69385c9c333903892421a7d16dea9e71; original global index 7845.
def localCycle00308 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 6568d2591a66d29beb88d85605f8311799f34f55e6d406da55ea8dec8de7e208; original global index 7887.
def localCycle00309 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 3 6, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 2 2, .triangle 27 1, .triangle 11 0, .gapLower 0 1]

-- Original cycle 65895be6d9b2ef37ea190a5c5c436263877f3e1b5e463731eec64ce83d607a7d; original global index 7898.
def localCycle00310 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 6, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 11 2, .gapLower 0 2, .triangle 5 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 66585d25e7fef8e8d45e62772cf4df6e67c1b914bfedeb870144a233b329149f; original global index 7959.
def localCycle00311 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 14 0, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 66915a741a60d550a8d8faba6ff90a5e984e9152599b8f881851d2761a7f79d5; original global index 7971.
def localCycle00312 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 5, .distance 0 6, .distance 0 4, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .gapLower 5 3, .gapLower 0 4, .gapLower 0 3, .gapLower 4 1, .gapLower 4 0]

-- Original cycle 66b60b1820266d6a67d2cb762d086539a625f21846d5f247f46fd6aa192840c7; original global index 7984.
def localCycle00313 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 13 2, .gapLower 6 2, .gapUpper 4 3]

-- Original cycle 67080219b8533e1d6010ac8e7f536a38c1909707a8914d738fa50e8f185f6711; original global index 8004.
def localCycle00314 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 0 5, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 7 2, .triangle 14 0, .triangle 34 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 67dc66a3fede68ed5a587439f98214c0ee87bcf93ba266cf9dcc4fbb67b13b8b; original global index 8073.
def localCycle00315 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, 0, 0, 0, -3, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 13 2, .triangle 14 1, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 67df4b7c1e52f0fb64bf84e5d3137e3919f8b6e4beb5ee5b0df217d579ae253e; original global index 8075.
def localCycle00316 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 3]
    constant := ![2, 0, -2, 0, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.gapUpper 3 2, .triangle 11 2, .gapLower 0 4, .triangle 12 1, .gapLower 0 2]

-- Original cycle 67ed54ff00d3b8f02c20b76583557ad6dd7aa7eb9c9e0e14993de39a46696962; original global index 8079.
def localCycle00317 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 681e9b352712f2c461cefeec00dc0b3f230427e700ea51a57ce9e489e92a77a7; original global index 8092.
def localCycle00318 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -1, 0, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 6 2, .triangle 12 0, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 6837905f812d15c047e199d09522a49aebfb21f5ada3ab0bddf2f6c8deb769d4; original global index 8103.
def localCycle00319 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .triangle 8 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 68a9d2bc2c78aecc05cb0a4d19578d2d3fa43980f057f0b8fdab4460aaaf4966; original global index 8141.
def localCycle00320 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 692617ac15a1e9788fccee33eb2ab6b0ace157fc2fa9bdc4e22b82fd882c80e0; original global index 8177.
def localCycle00321 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 69407bf57f26021a46d08a35c25ab01c4a4fcaaf40d3da0cc9838dd347ce625b; original global index 8187.
def localCycle00322 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 697b13f86a4b093026675fee1dc5e9fad49d3f75650a2a3f53db1b23b6836479; original global index 8204.
def localCycle00323 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 698af1f02b84b8a00977e8b2db6cfa0a5d54747e3ac2869874f997c9fceba94f; original global index 8207.
def localCycle00324 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle 69ab38917668c99938a713a269b33ad4917890d5054f7f12a155f8dfc9da75f8; original global index 8224.
def localCycle00325 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .gapLower 6 2, .gapLower 6 1, .triangle 23 1, .gapLower 4 0]

-- Original cycle 6a1756c5b622cf93a7d8907d976cae816ed6186761949278e37c3d597b93fdd8; original global index 8254.
def localCycle00326 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 0, .triangle 14 2, .gapLower 6 2, .triangle 23 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 6a34c3384a1366012f2175b2bb7fe49b839469b4de32dd662c1dcf1fb40d6c78; original global index 8268.
def localCycle00327 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .triangle 30 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 6a641175556600925a45dd80513f7fd0a0f1ebfc93d1a9eeff18c870c165e573; original global index 8286.
def localCycle00328 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 1 4]
    constant := ![2, 0, -3, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, true] }
  origin := ![.gapUpper 4 1, .triangle 34 1, .gapLower 6 1, .triangle 23 1]

-- Original cycle 6acf333a60f4713d289279c176fde67c0e8cc3c850abdd8b6163dfc91cf7a451; original global index 8315.
def localCycle00329 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 4 6, .distance 1 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 23 2, .gapLower 6 1, .gapUpper 4 2]

-- Original cycle 6bf428ac38e90a9aa0d33fbbcc41e560f3256d961243acfc3b0bb030f7df09aa; original global index 8415.
def localCycle00330 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 8 2, .triangle 14 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle 6c52e8b35653e2608f7c5a7067ea69774d1f2198d445956673f994666b89604c; original global index 8439.
def localCycle00331 : Cycle where
  length := 5
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle 6c6c812df7fa0e417a355404b5e87ab71e1acc3413469273d3f72db83c6c0b72; original global index 8440.
def localCycle00332 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 6cbbe1e824ae8244975495d202fc9d29165f52201df391bb015181c8fae2676e; original global index 8461.
def localCycle00333 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true, true, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 1, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 6ce06b846d44ef1f4d0abf86587968dd7c934a7b8debd46bd0573832621da0c9; original global index 8472.
def localCycle00334 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .gapLower 6 3, .corridorLower 5 6]

-- Original cycle 6e14df10ab926c65627f05af097e4a377118b43b9c3fb4833b77a44019924694; original global index 8548.
def localCycle00335 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 6ea02c6c6432c131e54db7968c2313fd879c19c3e60f780042307f075461a8ac; original global index 8582.
def localCycle00336 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -3, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .gapLower 6 3, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 6f52a793329b5c7d120a9795d3572306347b9d2bd5a8b01cee0eb16c26d06d05; original global index 8630.
def localCycle00337 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .gapLower 6 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 707027fae07ac5fe3c89f03cbfcb18949b52b5b4fb37f5987e7f9fd9d5e86d1f; original global index 8711.
def localCycle00338 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 11 0, .triangle 5 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 707e93db357412224c4d6965f33b104322fc255db61655d37c95037b146348c3; original global index 8715.
def localCycle00339 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 5 6, .triangle 22 0, .triangle 23 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 7159cc6c266d76d431c323c424a2e76bbd5ace94bea8b03fbae05319d2da74f6; original global index 8791.
def localCycle00340 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 25 2, .triangle 29 0, .triangle 13 2, .gapLower 6 2, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 71687360070439957e07f75c35309d1ae88e7e9bc435ddbb70387b462f5aea05; original global index 8799.
def localCycle00341 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, -1, -1, -2, 2, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 24 0, .gapLower 6 0, .gapLower 6 6, .triangle 32 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2]

-- Original cycle 736f870eac86f3eeb9da45be131d455f4e145aa1bc6848c39e4704a8078e353c; original global index 8947.
def localCycle00342 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .triangle 8 2, .gapLower 6 2, .triangle 24 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 73f03b5db40a9bda194ee6893fbe8d7c59c4af735e4cff0f3e27e7ac079fe85d; original global index 8992.
def localCycle00343 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 8 2, .triangle 13 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 7408dad13d7ebff7119c8bad89859cb49ca0e8adbd125c674f166658f2872dfe; original global index 9003.
def localCycle00344 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 13 2, .gapLower 6 3, .gapUpper 4 2]

-- Original cycle 74428463e9621c620d208c988029fcf0560c63093a7f44577e0488efc498ef7e; original global index 9018.
def localCycle00345 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 4 5, .distance 0 4]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 4, .gapLower 5 3, .gapUpper 4 3]

-- Original cycle 74a9dd26d7cddf9aad2cff0f79674c24b1b263794f0dbe445a9d92d3a58b5966; original global index 9036.
def localCycle00346 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 29 1, .gapLower 6 3, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 74ebb5a6ac75795a5c8cf1b8f55c76aa68e15c775a70b18603d7d838e92cc51a; original global index 9058.
def localCycle00347 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 5 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -2, 0, -2, 0, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true, true, true, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 14 2, .gapLower 6 1, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 74ef80be791f976f942b1633b184e5cf80cae7ec9d47fec23b1f31754eaa0455; original global index 9060.
def localCycle00348 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 6, .theta 6]
    constant := ![3, -2, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .triangle 13 1, .triangle 23 2, .gapLower 6 0]

-- Original cycle 75281524e9c0a8abfdbe604a1ce0b33b4ca59e2b0e8efe105ecd4a666dd116f7; original global index 9078.
def localCycle00349 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 75b9e7499df3b58072eec81ce795f05642f2302f984d42f8c3dc08a12efd5907; original global index 9129.
def localCycle00350 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 26 0, .triangle 5 0, .triangle 0 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 762327cb55202598a148613e35f8ee0dee6ab7497c4f61d2a819add671be37b7; original global index 9145.
def localCycle00351 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 772d7acf7424afdb54b42738e66e6ee69fd5e38f28f5546c234ef7378e78ae27; original global index 9224.
def localCycle00352 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 3, .triangle 5 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 7840523d6c8826a91b10e3f48494c82100cbacbcdb2c7def3221cda4c0196d2c; original global index 9295.
def localCycle00353 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 22 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Original cycle 78c05b65bc3dac91beb923a70bbf1d2a2760bd277c921316af7b88a7217fb3c8; original global index 9342.
def localCycle00354 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 4 6, .distance 2 6, .distance 2 3]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .triangle 27 1]

-- Original cycle 78c074af78725c6eee57bd8aabbf10212d61cfddcce7b8088ab9b1c056ca557b; original global index 9343.
def localCycle00355 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 13 2, .gapLower 6 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 79f65f7c3fb088d871977e12e60f6280afa61fe38e45d030b7b5c7d5cf821ba7; original global index 9433.
def localCycle00356 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2]

-- Original cycle 7a7cf0547b93446529ad44ce46f5d6ab360d18ba68dbdf7a6c22fd9be1f63230; original global index 9476.
def localCycle00357 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 2, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 7a7e06bce3fc454f3284a154ee9d473c6ce5fd5f5c4da0bcf69d3b833c510b10; original global index 9477.
def localCycle00358 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 0 5, .triangle 12 0, .triangle 22 2, .gapUpper 1 5]

-- Original cycle 7aa84e2a410758fbad6ab60565444ee229c5006e0b4dbe90dbf2b1b345b38026; original global index 9492.
def localCycle00359 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 12 0, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 7ae83c7379033f8fee4dcdc9610d09634d52c40fc6fe07eca3a4d671f68f7383; original global index 9514.
def localCycle00360 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 4 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 29 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 7b7faf316ac15257e0bc1520a192b509eb09e463307e743db4003400c6901d4f; original global index 9557.
def localCycle00361 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 7bffaabb34ab9289046255238b1de7612d58001534dc8a091db9e2135b2aa79b; original global index 9591.
def localCycle00362 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 7c818df7fa2ea47b4790ade403786363e107f48eafb7f8a4612520cc69e382a0; original global index 9635.
def localCycle00363 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -3, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 18 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 7c9ae54539a1b7e46e4a554d61b90c97b7579169f2d72aba3eab95fbc11bbc0f; original global index 9645.
def localCycle00364 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 7c9e282e9ee15eb42f3f4e3e72b5587f7b5a0ae3880332bdb0818786a626dbb6; original global index 9647.
def localCycle00365 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 5, .distance 0 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 12 2, .gapLower 0 4, .triangle 8 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 7ca0faced06c0fe49d774ec56bacb0123caad6da804bf30b15d93171c007cb83; original global index 9649.
def localCycle00366 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 2, .gapLower 6 3, .triangle 14 0, .triangle 12 1]

-- Original cycle 7cc5b77f7a37f9df1e0c248c48adda039326a8fc96cd6876375bd33cd98fb286; original global index 9665.
def localCycle00367 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 7d02253870ba1597ab951657dceec29beaf91b183ecfae277763d6af84ef02ac; original global index 9678.
def localCycle00368 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 2 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 29 1, .triangle 25 1, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 7d2946e18cb33b7e261a42db69550644d1ff438291c31bf156665bec2af6c663; original global index 9700.
def localCycle00369 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 0 6, .distance 0 5, .distance 0 4]
    constant := ![2, 0, 0, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, true, false] }
  origin := ![.gapUpper 4 2, .triangle 13 2, .triangle 14 1, .gapLower 0 3]

-- Original cycle 7d726b41f13f9e46fe40bbdef9ef053ba98eab82bbc9dd01fb89243a124f22fe; original global index 9726.
def localCycle00370 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 6, .distance 0 4, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![3, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .triangle 14 2, .gapLower 0 3, .gapLower 4 1, .triangle 16 1, .corridorLower 1 2]

-- Original cycle 7d8346ea6828de896e8020b4194f229c964bf40cbc6eb43bede45b794280bd87; original global index 9740.
def localCycle00371 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 11 0, .gapLower 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 7d883e3429f2966457bf6746403035c78a5c51e4dc46649cff9d3499b80dcb8d; original global index 9743.
def localCycle00372 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 7d9a5fe4ae9dfa53eb839809fb930eccb36cedcc14d1416db240baa91f22f2b2; original global index 9748.
def localCycle00373 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 7dae6b2f06d70bd19591e45fc7c42c317b64db862bd4e7c2a914c1fb6964799f; original global index 9754.
def localCycle00374 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 4 6, .distance 5 6, .distance 0 6, .distance 1 6, .distance 1 5, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 34 1, .gapLower 6 2, .triangle 4 1, .triangle 24 1, .gapLower 5 0]

-- Original cycle 7df2c0229aac2bb757f95457bc98782c8c2062b7ce3207f5f5f78b555146a31b; original global index 9781.
def localCycle00375 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 14 2, .gapLower 6 3, .gapUpper 5 3]

-- Original cycle 7e288f5d32c0a54ce241fa1715457a1638716314ce592bcab7958d66e0718e90; original global index 9801.
def localCycle00376 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 4 2, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle 7fbfdc4a43d215554221c96e4b9ca8ead07a804743d010d5d9b55c67f1deaca2; original global index 9907.
def localCycle00377 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 5, .distance 1 5, .distance 1 2, .theta 1]
    constant := ![3, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 4 2, .gapLower 0 4, .gapLower 5 1, .triangle 17 1, .corridorLower 1 2]

-- Original cycle 7fd1e7cb73e9404cf72a2087dae256679a7b55f0897469e2ac6e8c7266ec383e; original global index 9915.
def localCycle00378 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .gapLower 6 4, .corridorLower 4 6]

-- Original cycle 7ff4452e95c16a31ea90c619116c808300a190dda02dfbf6ffe24791329e387b; original global index 9925.
def localCycle00379 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, -1, -3, 3, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Original cycle 801fa73d78e92194e96e55980c6a3b23568bcc5fa0f5a7536e889f37ca7137d7; original global index 9938.
def localCycle00380 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 2, .triangle 14 2, .gapLower 6 2, .triangle 23 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Original cycle 81b3376ad3dd0a8f1ad23bb23b37e706535d22255e10adae992b963519ed8184; original global index 10069.
def localCycle00381 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 4 1, .gapLower 6 2, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 8213fcb3a4cc385b5ef5dca3229edd9742763373934459f14e7b7554134d874a; original global index 10100.
def localCycle00382 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Original cycle 8277f173c2187c87925a5b75a512824054a5e07adcdfd0005ba7142aca2800f4; original global index 10124.
def localCycle00383 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, 0, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 13 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 837a172ce8e2b0f5402b131ef9ba3f1e62b70f7d08de43dde2adb811fad282cb; original global index 10201.
def localCycle00384 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 83aea0d0c8d61258d042d8cc1a2f6a761b3fa5b4fb69c858ffcf26718287eef7; original global index 10221.
def localCycle00385 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .gapLower 6 2, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 83f572811fcb7e1836594081ec2ff6b91cd99cb8d1eeac5164d3f5d7389aa951; original global index 10243.
def localCycle00386 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .zero]
    constant := ![0, 2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 8 2, .triangle 14 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaLower 1]

-- Original cycle 8426bcfdd7ba816baa3471f9771ab7c6b49ef8d68a445a80cba4cb5c95d93346; original global index 10259.
def localCycle00387 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 844b97b5ed48ae278c5e67456928cae9efca356f8246f5fa5222c66a10ae2c39; original global index 10275.
def localCycle00388 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .gapLower 6 4, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 8524c5ef5f752180703ece070635db0d2a47d6f55161065084077d58a8150f28; original global index 10331.
def localCycle00389 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .gapLower 6 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 85bb7a6a1de3c4cf3dde4d83063030be996123edb6733f55116ebf3981d52cf2; original global index 10379.
def localCycle00390 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 12 0, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 8651aa78cda6ac96d40430b1ac70ce2b94f2e2d6a640ab9bd5fa2504a32f0293; original global index 10414.
def localCycle00391 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 2, .triangle 29 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 86917d18c63d74768fabea9a7c65b25c2d1712d9dbb29a4b215d670a6fe46740; original global index 10432.
def localCycle00392 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 0 6, .distance 0 5, .distance 0 4]
    constant := ![2, 0, -2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 4 2, .triangle 13 2, .gapLower 0 4, .gapLower 0 3]

-- Original cycle 86ace735a625476cb46235c0447ea361f208ecdcf234fc7a14638e494351e398; original global index 10444.
def localCycle00393 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 0 6, .distance 4 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 13 1, .triangle 34 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle 86c71a725212b7ad2a61afab403ffc097a242b59923d27e5b6dfaa6abd213ad9; original global index 10454.
def localCycle00394 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![-3, 0, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 0 5, .gapLower 5 2, .triangle 24 2, .gapUpper 1 5]

-- Original cycle 86cab293930a996b292724180a2ad69384aa2d63714ab2a18d9d3ad05ea37fbc; original global index 10456.
def localCycle00395 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 2 2, .gapLower 3 2, .gapLower 0 1]

-- Original cycle 86fa5dbc6109c6f18c014432d15dd4b578679106ea4a635c91dd105b94b31a74; original global index 10469.
def localCycle00396 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 2 2, .triangle 12 0, .triangle 34 0, .triangle 24 2, .gapUpper 1 5]

-- Original cycle 870dab8850d3b1db6256fff20c472dfe7fe3b2343b0a05e11803070af324aba8; original global index 10477.
def localCycle00397 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 4 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 13 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 875c31a16d0748a0c3959a8ce7533480ef373f35873d8b7420356b48db7e0c29; original global index 10499.
def localCycle00398 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 87ef0d373bf60409f15f10e9b7f3d7f8b1de0312a309c71edb3671b30cd2a11d; original global index 10534.
def localCycle00399 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -3, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 87fa0cc5654cbcddb2cd071ba59f4b95912f8117536be96c6e0981d2a220782d; original global index 10540.
def localCycle00400 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 0, .corridorLower 2 4, .thetaLower 2]

-- Original cycle 886f83d96a9c82ed34919c6a943835106f169d5c5c97c6b0891873492af54621; original global index 10571.
def localCycle00401 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 88bb091058a674f0f03910d2f943817c3eb2ab0017712126d8cbcd73e9035abf; original global index 10593.
def localCycle00402 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 89918dad4e22eb38e5fd942e4951c07b111bb7ee6184f5302daa21c1feaa34ed; original global index 10652.
def localCycle00403 : Cycle where
  length := 3
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 6, .theta 0]
    constant := ![2, -2, -1]
    coefficient := ![1, 0, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .corridorLower 0 6]

-- Original cycle 89d9449943e123803fb8f65410096d2157cc031c0eaf687ed2b744b9d5356d31; original global index 10677.
def localCycle00404 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .gapLower 5 2, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 8a027ed5e9a593becc99049030d659b8bd577e9f5ab3a30784ed57641077658f; original global index 10696.
def localCycle00405 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -2, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .gapLower 6 2, .triangle 13 1, .triangle 12 0, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 8a15caaf11af06e5b9616f39a9390965cefeb1d9e216ec546c86a09c729f9621; original global index 10701.
def localCycle00406 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, 0, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 8a505ed99eaa37a1c0a0a1ac25c5956f79f92cfb15dd7f1e2285a5bbcdd564a7; original global index 10718.
def localCycle00407 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 8a5f5f91fd30c8de88a590c1eec83242d9b5f149ca549488cd50dab47fc19777; original global index 10722.
def localCycle00408 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .gapLower 6 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 8b3d7e26bb0591d10e16447f6d9a54c5597eca9b205cf30b36c7aacfc3c13f35; original global index 10788.
def localCycle00409 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 3 4]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 3 4, .gapUpper 5 5, .gapLower 6 5, .triangle 32 0]

-- Original cycle 8c316aa76d7b6ff22d15616bedd1f39f6965f0be5ff3225732052a4e9198b0e6; original global index 10849.
def localCycle00410 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 13 1, .triangle 23 2, .gapLower 6 0]

-- Original cycle 8cde91d3d290ac00111edf65248a2acf1df4009cc70deef768751e0f0e30d599; original global index 10896.
def localCycle00411 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -2, -1, 2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 12 0, .gapLower 0 2, .corridorLower 0 3, .gapLower 0 6, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 8cea3457b47fe762db8ee5458efd1d7eda309b59a55119ba2030f159f19b8b27; original global index 10900.
def localCycle00412 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -2, -2, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .gapLower 6 2, .gapLower 6 1, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 8debfabe7c7b8d3d96245a84b40fccd7761d95f7eb2279939268665b675ec5ae; original global index 10988.
def localCycle00413 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 2, 0, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 8e4e15239ca4fb3a0b79728d6448b200d194d68177cca691906e3bde1a42c18b; original global index 11018.
def localCycle00414 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 0 6, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -2, 0, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.gapUpper 2 2, .triangle 8 2, .gapLower 0 3, .triangle 9 1, .gapLower 0 1]

-- Original cycle 8e86fcd4bf899f9c000582aea43784d9fbf9c97b2ac7efd45fb91c60877e79b5; original global index 11027.
def localCycle00415 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 13 2, .triangle 14 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle 8e8e26f5231900cabb0a59829e30fe7c0ebea3d0563b1fc8d6609d7c4a14236b; original global index 11031.
def localCycle00416 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 8ef6c1a600ac409ff10a14d3a5d605c6c99c114c5a983aff12653626f9fd2b5c; original global index 11060.
def localCycle00417 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle 8f88af7ca4e59b12363c88a9ff0c3b48e15f927e3b4fa8547b5cd7b16806d458; original global index 11106.
def localCycle00418 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 4 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 13 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 8ffe3c4dd765862d65baa3a28d344ab403fb8570cd56bbe8db4350136b96d1f7; original global index 11147.
def localCycle00419 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 9005cf2dda7b81d7b67dbd7610384c9565d29198a1a1609c5f0abe9a31201751; original global index 11149.
def localCycle00420 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![2, 2, 2, -1, -1, -1, -3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.gapUpper 3 2, .gapUpper 3 3, .gapUpper 3 4, .triangle 33 0, .triangle 34 0, .triangle 12 0, .gapLower 0 2]

-- Original cycle 9052a3946a0579e242e88252072fd3a0b81968ab29fe0e5ed93adb4060423b1c; original global index 11172.
def localCycle00421 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 0, .triangle 24 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 90aa8200ae7ac9bf3b79cffd607c76569aa1dd1b23439e146cbaed8f002ad7b4; original global index 11202.
def localCycle00422 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 4, .distance 4 5, .distance 1 5, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 2, .triangle 12 0, .triangle 22 2, .triangle 24 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 9120c5e00a92cdf582f0e6fc10b0f7df82cdee50e6171e7f182fc5fbef92c102; original global index 11238.
def localCycle00423 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .gapLower 6 3, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 91248e6d5002d4e0380442c6291a0742d3badb869a442bdf2ea7106feded7933; original global index 11239.
def localCycle00424 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 912bce598e8287c27671c875a8d9af363ec54770052bd1b3e43b345f3a2010c3; original global index 11242.
def localCycle00425 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 5 3, .triangle 14 2, .gapLower 0 3]

-- Original cycle 916075d0ba96281aa5f510cdbc083b0f5b082a6ae95feadfa72db13eec7aee2b; original global index 11261.
def localCycle00426 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 919264a094260ac285af026f63386f4cb1e51b29c07b916d21eb5a11f7494fa6; original global index 11279.
def localCycle00427 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 91efcfc67ccf5d9cc5c516555d0585c497cc2d595431988d19b0255a3d30ae12; original global index 11312.
def localCycle00428 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 8 2, .triangle 13 1, .triangle 34 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle 9251a1d602f1b535359ca0d5096fc6d60285e951b52603b26c1e8995f77fcd0d; original global index 11334.
def localCycle00429 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 0 5, .distance 0 6, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 7 2, .triangle 14 2, .gapLower 6 3, .triangle 34 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 92d75a8ef7140ab38abccc3690b425a9496883601a0efc1a844ce3bcc1eed3d5; original global index 11383.
def localCycle00430 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 6, .distance 0 5, .distance 0 3, .distance 1 3, .theta 1]
    constant := ![3, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 2, .gapLower 0 3, .gapLower 0 2, .gapLower 3 1, .corridorLower 1 3]

-- Original cycle 92f80905760f63107e3325c52a0640fd3a2a3321c80e4e42e444f544e47950e4; original global index 11390.
def localCycle00431 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .triangle 23 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 92f9a3c7abd0c9add8a00703fa45390dae9c957e19a6e8f3ff5899338a334f08; original global index 11393.
def localCycle00432 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![2, 2, 2, 0, -1, -1, -1, -3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false, false] }
  origin := ![.gapUpper 3 2, .gapUpper 3 3, .gapUpper 3 4, .gapLower 5 5, .triangle 30 0, .triangle 34 0, .triangle 12 0, .gapLower 0 2]

-- Original cycle 92fcf699d5e467d789c6bd47d20f81ba4b931c91341cdb026fa36c0eb3946d8d; original global index 11398.
def localCycle00433 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 3, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 11 2, .gapLower 6 3, .triangle 24 0, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0, .thetaLower 0]

-- Original cycle 9329cf71b20504ca0871dcd6c5119a5f20854e7ef9499cdb191f8ea4a86a56a3; original global index 11409.
def localCycle00434 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 27 2, .gapLower 6 4, .triangle 4 1, .triangle 23 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 93674c84354cffe64794ad68669cc337cc332c4fd492bb65d60d84409e446c64; original global index 11433.
def localCycle00435 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 0 5, .distance 0 4]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 4 2, .gapLower 5 2, .gapLower 0 3]

-- Original cycle 937ec22db98ddeeca3e034033861c7cbe6761ba7aef79e944bcf62d0a6e6474c; original global index 11443.
def localCycle00436 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 4 1, .triangle 23 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 9390ec316ac372d40fc784547bfac91964cb8cddcf0b974fb64ded3b02a854ae; original global index 11447.
def localCycle00437 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 93a791f11b3bc006e07b52f4658771507ba7f4ee41f5b268093eceddf3525bba; original global index 11454.
def localCycle00438 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 4, .distance 4 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 2, .triangle 13 0, .triangle 23 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 943e04f726932779e18d20ddcaafdacdcf2058411b735a8c87157baa8f7d58eb; original global index 11501.
def localCycle00439 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .triangle 23 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 94c8a05f4f61c9551ed4b6f466223f48c3b66904e0ff85e6d5c5abfdf5e866cc; original global index 11548.
def localCycle00440 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 4 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 95026455ee3cfa1f9c43d0fb1ba0f17a21ee8e86246feea7bb4adf1a5139c0c5; original global index 11569.
def localCycle00441 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .gapLower 6 3, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 9511803635550d287a5987dacb66412894fa49cafeab435f3e689c508fed2f1a; original global index 11577.
def localCycle00442 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 2, .gapLower 6 5, .triangle 8 2, .triangle 13 1, .triangle 23 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 95520f92c5165c7ef7adb4a35060f6745149137b98a4c37956314f527bb3137f; original global index 11601.
def localCycle00443 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 955afde7b114b49c5839e93993535b063bf6f4e77f8a53e19ce22e6127425f65; original global index 11605.
def localCycle00444 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 0, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 95ec9a33d679f76d4286f7d607b08d158bce3e7582d8db064296f3e0c81afffd; original global index 11657.
def localCycle00445 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 0 6, .distance 5 6, .distance 1 6, .theta 1]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 12 2, .triangle 14 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 1 6]

-- Original cycle 95ef3aaeb29308dc6538f754dd59019e7581a2ac53dc7fa92203b5e0c41bc4c8; original global index 11659.
def localCycle00446 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 2 2, .triangle 13 0, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle 97179ecfe84b2ddddbf568ae51dfac095792fb2164d1838128ccbe0de4afaf6c; original global index 11743.
def localCycle00447 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .gapLower 6 4, .triangle 14 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 975157d0a79c7a1f514d7ed1746316537c1e24d47e97b25758adcfcaadefcdd6; original global index 11759.
def localCycle00448 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, 0, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .gapLower 6 4, .triangle 13 1, .triangle 23 0, .gapLower 4 0]

-- Original cycle 98657424e3afd1bbacb8ad397e8efe9b525bc527c07a7cc7b3cadf07c27be6bc; original global index 11835.
def localCycle00449 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .gapLower 6 4, .triangle 13 1, .triangle 34 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle 989fbf75946aff2bd75ea9a7ef5130dfb4fdb119045a0dfe8c579d32811a20bc; original global index 11853.
def localCycle00450 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 5 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 30 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 98e99ef1026f4e3aedccfeca264faf5a3b06eaeb23cc259dda0f83856e3396d2; original global index 11872.
def localCycle00451 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 98eacf836d12e86e39517d85adc64bb63a05973c270204ac110a1848e36a79d0; original global index 11874.
def localCycle00452 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 8 2, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 9923a9adc189d73fcdadbfdc3d5dfa57c326366d7e067c51f09b1db8e0f0e5e1; original global index 11892.
def localCycle00453 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 994c99f3b7736bed44fe8b09d554e92a01a031e7768c0761d7579ce08525a9ef; original global index 11902.
def localCycle00454 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 4 6]

-- Original cycle 9994ff1edc4a2cf94470d94b5ee838cf33e40707b9120a78a92a394fb7698f15; original global index 11924.
def localCycle00455 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![0, -2, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true] }
  origin := ![.triangle 13 2, .gapLower 6 3, .triangle 34 1, .gapUpper 5 2, .triangle 12 1]

-- Original cycle 9a19d9381378a8ac25892afe41e0b3333ecf9d1a0831c4c919e53ce6402228d2; original global index 11966.
def localCycle00456 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapLower 6 2, .triangle 13 1, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 9a4812b79d44b7bcb6cbdec1a4bda1f22f8974bd3c8c2dd8786ec892dbe58f3b; original global index 11989.
def localCycle00457 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 9ab101ecb0155443db42908a20a0b708f26cdcff4326c9354fcf3d21f8dad6da; original global index 12021.
def localCycle00458 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 5, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 2, .triangle 14 0, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 9ae95b0348c82b43a860217f3bfc6631801bfbacff122a7882aafb76ac2a859b; original global index 12038.
def localCycle00459 : Cycle where
  length := 5
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .theta 6]
    constant := ![3, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 0]

-- Original cycle 9b36a2b3ff5758d73ff6c8f1e6c7ab0e28c5f58ba8e69f25e392be6ae86fd6c9; original global index 12070.
def localCycle00460 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 6, .distance 0 5, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 13 2, .gapLower 0 4, .gapLower 5 1, .triangle 22 1, .gapLower 4 0]

-- Original cycle 9b963ea0027d87d54a0a94152a8756a92cea87aa5d94610f818792dc8f799b3a; original global index 12102.
def localCycle00461 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 2, .theta 0, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -2, 2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 13 0, .triangle 6 1, .gapLower 0 0, .gapLower 0 6, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaLower 1]

-- Original cycle 9c1c168060fdf82a8f03c6fdd576018df0c27e83e6d4915c3367e9cbabeb0602; original global index 12145.
def localCycle00462 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, 0, 0, 0, -3, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 12 2, .triangle 14 2, .gapLower 6 3, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3]

-- Original cycle 9c487ab1b62cc9fb40814d5fe1fa9a779750e90028d1531d9283a1690f08cae1; original global index 12159.
def localCycle00463 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, -1, 0, -2, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 9c87cdaecfbea10d67e9ec69b625be28b6d33c6f0e3287fbe53682cf98f85419; original global index 12173.
def localCycle00464 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle 9d17c7b3beb460007ce71dbde1151b32af2e774bbd733fd43870c13b84bcbdb3; original global index 12218.
def localCycle00465 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .theta 6, .theta 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, -1, -1, -3, 0, 3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .gapLower 6 0, .thetaNext 5, .corridorUpper 3 5, .triangle 33 0, .triangle 30 0, .gapLower 2 3, .triangle 15 0, .corridorLower 1 2]

-- Original cycle 9d9d0295466fc4bd13568c9c9384e92bcc1f9a6d0d0dcc59d50945ffbb772a45; original global index 12255.
def localCycle00466 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 8 2, .gapLower 6 1, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 9dec3ed9aa624df4a7faffe79cb3f5782c2c1977eb2ca442e18ba4bd591fe97c; original global index 12289.
def localCycle00467 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 13 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 9df343d87a2edc15e67a1109399231770b8c594621bb60d70fd64eb8ee659fb6; original global index 12292.
def localCycle00468 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 14 0, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 9e29f852da5526fd25644f300b155c23eea80e3d99effbb1f9463dd33d834d1f; original global index 12309.
def localCycle00469 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 12 0, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 9e8269f1c95a9c521a339ad678f779d6d7ff8af51076ecf39dff5f9003b36326; original global index 12346.
def localCycle00470 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .theta 1]
    constant := ![3, -1, -2, 3, 0, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapUpper 2 6, .thetaNext 1]

-- Original cycle 9ea5e0420f6b2f6e4988aa92c7cee6e428793d3c0ac51000573ff4b8967577b7; original global index 12354.
def localCycle00471 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .gapLower 6 2, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 9ee4adaa911f515564c1168a0708be699840d39138d2eaa7c88316086166c407; original global index 12371.
def localCycle00472 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 1 6, .distance 1 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 1, .gapLower 6 2, .triangle 23 1]

-- Original cycle 9efd090581a26d03f4412f6557499945dfb2da8b54e9349818a5acdb8e1ff231; original global index 12381.
def localCycle00473 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 6, .distance 0 5, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 14 2, .gapLower 0 4, .triangle 7 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 9f0c67b67815657e31009780b3f755d5394cb6925bd2b7c5f0d4adc3008f83e8; original global index 12384.
def localCycle00474 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 15 2, .triangle 19 0, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle 9fbbce0c68a2e514e6295b5437c9b1113de9171a5e199e43326c005ecb30dd87; original global index 12432.
def localCycle00475 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 0 5, .triangle 14 0, .triangle 24 2, .gapUpper 1 5]

-- Original cycle a02904a53d2981ef9ade430156880d13d39cd53056e9deb8bf9f9a39d53dbeff; original global index 12459.
def localCycle00476 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 2 4, .distance 4 6, .distance 5 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -1, 0, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle a0444641fbfcccb3bf2fec6664fe72526118513318f8d1e7d16433555156fe2e; original global index 12470.
def localCycle00477 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 0, .triangle 34 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle a04b2872f8b27e47efe2f3504e443a523ace81231e7703e47cb173bf540199dd; original global index 12472.
def localCycle00478 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 25 2, .triangle 29 0, .triangle 23 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle a0de8304a76adc5df0b0f3dc985051cf1bfd4bf15c4a3e42cd84c73c174ea177; original global index 12512.
def localCycle00479 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 2, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle a10a7108c95d1b63efae227ef44347dbaa08ac447c695def6f380aeedf7b0233; original global index 12524.
def localCycle00480 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 4 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 29 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle a123562e9ae584bcc9a1a55fc4401a894eb0347c927a895b0964a16bf69505de; original global index 12531.
def localCycle00481 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 4 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .triangle 23 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle a219396016780754e613446cbe7a43ce79cc4d476613d758941413ccd4f30751; original global index 12610.
def localCycle00482 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .theta 2, .theta 1]
    constant := ![3, -1, -2, 3, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, -1, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 2, .gapUpper 2 6, .thetaNext 1]

-- Original cycle a223113f31f30742beeda46ba6ea3ca002da2ada331d88a3fe6195869569ac6a; original global index 12614.
def localCycle00483 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 6, .distance 1 6, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -2, 0, -2, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 27 2, .gapLower 6 4, .triangle 13 2, .gapLower 6 1, .corridorLower 1 6, .thetaNext 0, .thetaLower 0]

-- Original cycle a273afe3639a278398e6da5e55b962c3bf7d83bfbf7d46cf50edf7306d1ec4d7; original global index 12637.
def localCycle00484 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, 0, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, true, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 1, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle a2e5d4bf4cb84d0da3bc18c6b7027ee576232ccc5483d89c7e4a49d51d570b52; original global index 12670.
def localCycle00485 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .theta 0]
    constant := ![2, -2, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaNext 0]

-- Original cycle a35d180f90bd1ee1dafbab8482915ff78365af7a99ec1d02fb5dd76951c1fa25; original global index 12698.
def localCycle00486 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 14 2, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle a3cd350e8ee9b16466c9dca0e2c2b9da285c5516613b1d834b52e417528122cc; original global index 12738.
def localCycle00487 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 8 2, .gapLower 6 1, .triangle 23 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle a3d6c949969f21779a9b721a4b03b98a658865137f771ce03cf1bcde1068a626; original global index 12739.
def localCycle00488 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 5, .distance 5 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 12 2, .triangle 14 0, .triangle 24 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle a4418d9a4066eb6969cc4cbefa08f117b16e3984ace6ed765ce0d64726c7d04b; original global index 12766.
def localCycle00489 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 0, .triangle 30 2, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle a47864fad61e85518215b9473c346f4a840460aa3516cac5c1d3b5772bfd1951; original global index 12783.
def localCycle00490 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![4, -1, -1, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 28 0, .triangle 29 0, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle a4fa5788e9f549fe7d71a861691634dc8137651deee240072ab55213db9f6202; original global index 12821.
def localCycle00491 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, -1, 0, 0, -3, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle a5124882ed2108b919f11f21e6895f6f08eed2fd8ff7d15ffe67aee89cbd50eb; original global index 12831.
def localCycle00492 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle a537e3acfed017ab7bac0fb914375f7fe756b7732152efca91045cba6551135d; original global index 12835.
def localCycle00493 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 12 0, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle a5492d4ed8575a6ae858facee5c1b5f82386a4b8d6e26c3f78081edfa301f1b8; original global index 12841.
def localCycle00494 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .gapLower 6 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle a57af7a60f30968dcf15141346c3d7217f43c03319008a42f722ce755724adae; original global index 12859.
def localCycle00495 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 2, .gapLower 6 5, .triangle 8 2, .triangle 14 1, .triangle 34 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle a61d3ecfa75f0c0cf53917ee9dad87b1b35529fa532fe2f2e3b34eeda541e603; original global index 12906.
def localCycle00496 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .triangle 8 2, .gapLower 6 3, .triangle 24 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle a6c8275deff9605f5ddb5682ad19570cbb7c4e3f6ed00fcb8d45c928f2bd01ea; original global index 12955.
def localCycle00497 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 0 5, .distance 5 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 7 2, .triangle 14 0, .triangle 24 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle a6e1ca3b68052b3d27eb8f8ffb678eb49580d6bcdfb162767687e9d4d6e6f566; original global index 12961.
def localCycle00498 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 13 1, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle a6f2e43be5301f7c353ceed3ac409531089ce3951dd1dc7b51d444d1996fc6db; original global index 12972.
def localCycle00499 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .triangle 14 1, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle a7147a826b79c682c1dc4a938603fa205b2e3ff1d21cfca83784e6f235ea803d; original global index 12987.
def localCycle00500 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .gapLower 6 3, .gapUpper 2 6, .thetaLower 2]

-- Original cycle a722b9d51f00748db8709a980f60a604fb859ff762a7f3ed7019fe41d871794c; original global index 12993.
def localCycle00501 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 12 0, .triangle 9 1, .triangle 5 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle a740bc961f58196f486c53da10333b8d3d37a576f87c63e896b6e1a985e8d8b3; original global index 13007.
def localCycle00502 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 4, .theta 4]
    constant := ![3, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 29 2, .gapLower 6 2, .triangle 4 1, .triangle 23 1, .gapLower 4 0]

-- Original cycle a790306f75699d641ca5399fc564c3fb0fc903f52d764438a1983f5364ad5a6e; original global index 13041.
def localCycle00503 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, 0, -2, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle a8f4c74c954ed4ff6a35ef4f7d253fec31d946e865dff617df3eea0269965db2; original global index 13153.
def localCycle00504 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 27 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle a913ee4fe2e2c5b822f1ac5151199a0cb8cb7a6f1d26b85a4a7d07e2aae75496; original global index 13164.
def localCycle00505 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 5, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 30 2, .gapLower 6 2, .triangle 4 1, .triangle 24 1, .gapLower 5 0]

-- Original cycle a93f39d40601e61fd37a78801fd7279a720eb88720f1d0ea1293989b3bea2289; original global index 13177.
def localCycle00506 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle a9707215f99a8e69d5fcd6ef958d61def534f35a301e1e20c240afc21aadd29c; original global index 13190.
def localCycle00507 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 3 6, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 33 1]

-- Original cycle a9d65cc1f77f9b9098e5cba8ee7b8a186f118ff122d748f1d163f360cdb78485; original global index 13223.
def localCycle00508 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 27 2, .gapLower 6 4, .triangle 23 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle aa6f21d32defeaf71205d3e7d943f59791f3819aa367415301eb227aaac84206; original global index 13276.
def localCycle00509 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 5, .theta 5]
    constant := ![3, 0, -1, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .gapLower 6 3, .triangle 8 2, .gapLower 6 1, .triangle 24 1, .gapLower 5 0]

-- Original cycle ab30e26e1f51eb27efd2bd77e7ec4e904d2ea947021f1586f6917cc6488b31ac; original global index 13335.
def localCycle00510 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 1 5, .distance 0 1]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 3 1, .gapUpper 1 5]

-- Original cycle abced89322acb3772acd4b92ff2246aa533971ed8b3f3de795b848bc6c149adc; original global index 13378.
def localCycle00511 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 4 2, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 2, .thetaLower 0]

-- Original cycle abd345445672d63f2da10766fa098ea38f96f2160a10a76281e23f9accadbf98; original global index 13381.
def localCycle00512 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 12 0, .triangle 6 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle ac2db8a843061ca8662e9859ff54b7faf4a657b82f6b7ea09beaec08289ab060; original global index 13422.
def localCycle00513 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![4, 0, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle ac44487e4cfbb12497191d642bc08ec23e69b9810d4961c5cf1d2e2f27cb3829; original global index 13429.
def localCycle00514 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 13 1, .triangle 23 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle acca2368ac7ccb7ab45600d0cfa953e74d4213571afbee35d9dc7a844d377cb3; original global index 13470.
def localCycle00515 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 2, .triangle 13 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Original cycle ad6e3af5986ba600f628785340b1e9163d1cc1aa3945a76f9fb02458362681e1; original global index 13532.
def localCycle00516 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 8 2, .triangle 14 1, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle ad8e1d1c523fe8a3be0053e35ff7c5d86861e45807a7c3576a10b29bedba0774; original global index 13543.
def localCycle00517 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 2, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle ae007b9d3e4dea8e90a3c980cbe06b4187286854deefeea020d9c90ab9d3623f; original global index 13576.
def localCycle00518 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .corridorLower 4 6]

-- Original cycle ae0d3e85487a3700c2f89194323281ab4f27357163cd310e32a75bdaf2626b95; original global index 13581.
def localCycle00519 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle ae733903d8601094c91de934965094c52e3cb75430a457c060b3a089dbcbc5fa; original global index 13616.
def localCycle00520 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle ae80940495f6708f80a02bd711b4daf62d2536fad54af12d094af2bec9e0b6de; original global index 13620.
def localCycle00521 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 13 1, .triangle 23 0, .gapLower 4 0]

-- Original cycle aed6bc91695bcbe7bd38cca6d95e52891b873ced090a9908150349b04f55513a; original global index 13649.
def localCycle00522 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 13 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle af0d6e9717ad64d30d3c037f28f7017d827030706c2e7ec10522896a9d2196ca; original global index 13666.
def localCycle00523 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .gapLower 6 2, .triangle 4 1, .gapLower 6 0]

-- Original cycle af39ccf01c0f3c754da4a556d7cfb82a2e41088a8beddcd57affe62d978383c2; original global index 13687.
def localCycle00524 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle b0431d8a8ed5872fd9143600a33b547fa26ae6ae9af73935c49e1ec5b62faf17; original global index 13762.
def localCycle00525 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 2 5, .distance 2 3, .distance 0 2, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 30 1, .triangle 26 1, .triangle 5 0, .triangle 0 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle b0b87c15af648e8ca3b7bd3449be6c8beb1224c1abaa1bc67128d07a71544743; original global index 13799.
def localCycle00526 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 6, .distance 1 6, .theta 1]
    constant := ![3, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 2, .gapLower 6 2, .corridorLower 1 6]

-- Original cycle b16a77730c01b6ee89246231926f22f5284a7aca241140a61d247dab607dbb30; original global index 13863.
def localCycle00527 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 2, .triangle 12 0, .triangle 22 2, .triangle 24 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle b193d891f2c03f198fa0a38d0aa1049092719bede1a61dbfa64658c930796627; original global index 13879.
def localCycle00528 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle b1db54ea474e5ecc335a42ee05e83a5f081f299c24a1f4202ddbc7f2a1e66f11; original global index 13903.
def localCycle00529 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 5 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 33 1, .gapLower 6 3, .gapUpper 2 6, .thetaLower 2]

-- Original cycle b1f1e451f297857f2fb52f6ccc839f7b1306eda142cc24532e66a86a81ae1ebf; original global index 13906.
def localCycle00530 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 34 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle b245d91c044fb08a346a126fc2dc94cf79e2834f3ca9a8a5713e8e38972c17dc; original global index 13931.
def localCycle00531 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, -1, 0, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .gapLower 6 3, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle b26d6a8816dbe4559c8f90192dcbad277109050188cc0319ef4290bfc62671fd; original global index 13941.
def localCycle00532 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, 0, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .triangle 14 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle b2fbc6685291b19a8bb9ccedeff24b72658bdaf012f6ec5098b922b1ca67e33e; original global index 13989.
def localCycle00533 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 8 2, .triangle 13 1, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle b3fc8a59439ad918d27e1723c487f0af993bae50978782fd04b19a02d5fada11; original global index 14056.
def localCycle00534 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 3 2, .triangle 14 0, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle b50fa235b2e93d0310608b62e429469aee5c95944d85ac41219e33e04dcc2cac; original global index 14142.
def localCycle00535 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle b5337716f14445e9b09a7603bb119b775cbcf567329f95f8f024124eaf41e52f; original global index 14158.
def localCycle00536 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 5, .distance 0 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 2, .triangle 14 2, .gapLower 6 2, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle b564882c7bf962e7ebe3e5ad7369363de92489c19b0271a4a3deb77351980837; original global index 14170.
def localCycle00537 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 29 1, .gapLower 6 3, .corridorLower 5 6]

-- Original cycle b564e81acb91cc0d438ec8773eddf21d975961ca6699697cb802bffe1d52173a; original global index 14171.
def localCycle00538 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 23 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle b58c0fef5a6c7909ca5b4c8b2d775cb431421466d2254799c0f3cf95a5ed16b8; original global index 14187.
def localCycle00539 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle b5ce4a6cf18a2946974b6421d593c7293217f87e34188b74f1a15496901b7f9c; original global index 14204.
def localCycle00540 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, -2, -2, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .gapLower 0 4, .triangle 4 1, .triangle 23 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Original cycle b8843a7f0c257ba5925d2252dc68d2c0400954280ce5659c11b2a72c21889d92; original global index 14398.
def localCycle00541 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .gapLower 6 3, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Original cycle b90f5edb37ee387e62a13c831817d6f87c052b05e0cfcc8dbdd8d497567d180d; original global index 14440.
def localCycle00542 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle b98e9331ebb6c3859a468cd1879d2131680c1bbf21b32eae3de46372edc2d58b; original global index 14478.
def localCycle00543 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, -1, 0, -2, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 8 2, .triangle 14 1, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle b9928885639c4e833475d5cfaf47dcb46ddca94b0823e8ef08ac650a633cb95f; original global index 14481.
def localCycle00544 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 5 6, .distance 2 6, .distance 2 3]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .triangle 27 1]

-- Original cycle ba37aaa228d27d06a90e34c73f7158193d91b66cab66a6e0cea768f669cbb9f0; original global index 14539.
def localCycle00545 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle ba6af48a4380f505c67fca5b574ebfee59fe96c9d93656155599c1b973ff9cdf; original global index 14557.
def localCycle00546 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 5 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 14 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle baa146e66d5029bcb3f3e44a8d414f5660e2ba86d99f69552bd70961aeb6f2ed; original global index 14573.
def localCycle00547 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 18 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle baa34d8b82f43968d1f1cda690962187b41589c35d2fdd15725ab900b560d1ff; original global index 14576.
def localCycle00548 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 23 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle bb0160859db7a85b1fc594910ca278da831f62f5c3a9af98fe9bd09bf4ce7661; original global index 14604.
def localCycle00549 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 4 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -2, 0, -2, 0, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true, true, true, true, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 13 2, .gapLower 6 1, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle bb59ca0b500a3bd8ecb0d9d7671b9df6a2280dd416df76b45904edbfab4df1ff; original global index 14626.
def localCycle00550 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 4 5, .distance 3 4, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![4, -1, 0, -1, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 31 0, .triangle 25 2, .triangle 29 0, .gapLower 6 3, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle bb62f04c6725b6bcaddb4244b52f7d5426b944f373b1c921b875da631ac82016; original global index 14630.
def localCycle00551 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 22 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Original cycle bd62dca6c00996f0ff464977b6355f56d4ede6bf393c33ab41ea3619ba548b80; original global index 14771.
def localCycle00552 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .gapLower 6 4, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Original cycle bdadcc28edea0d2c0d0c684c197c258e7697f1375aef4ff94dd2c6a77feca37d; original global index 14796.
def localCycle00553 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 0, .gapLower 6 4, .triangle 8 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle be0c2f212629f48855a00ef42318870c1d4491d584331f34343c8bde429f916b; original global index 14820.
def localCycle00554 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle be4e0437d3d3ab28e33ffa145500b174c77c1d6f1bae88f86487f5969d054878; original global index 14846.
def localCycle00555 : Cycle where
  length := 4
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .theta 6]
    constant := ![3, -2, 0, -2]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 21 2, .gapLower 6 0]

-- Original cycle bf78e1e2d837cd99c9143f4ea19976cc673fe9b67afb0d74a9f306e70eb1966c; original global index 14940.
def localCycle00556 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle bff412667585e894f7240b05f51b37d980eaa5e01c46febcaa0ed1b88a0c6311; original global index 14981.
def localCycle00557 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 27 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle c001d7055cd3870c9bbb5e72194f3bc03c3a0b7633d9b8d6e5b1cf125987adc9; original global index 14988.
def localCycle00558 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 3, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle c0e4176038f0c55ef1c24ce94391d38e04d99b0450e52577ed742493bc81fca2; original global index 15058.
def localCycle00559 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 0 2, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle c142898dfc6f47d74233c96055563e8002d56320b4b67eec3094f0b37b3c6ffa; original global index 15086.
def localCycle00560 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 4 5, .distance 0 4]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 4, .triangle 12 1, .gapUpper 4 3]

-- Original cycle c16e57e78af6521914aa2b16788953e60bfa6a60606655deaa52ad5cfa53b514; original global index 15103.
def localCycle00561 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 5, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .gapLower 6 2, .triangle 4 1, .triangle 24 1, .gapLower 5 0]

-- Original cycle c1f1796e8f6048034f9dfb8f954ccaa41042fba7898db94652acba991e2643c6; original global index 15143.
def localCycle00562 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 8 2, .triangle 13 1, .triangle 23 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle c22294db5045d37782194764fe84def24f2d69f9a6fbfd6c0630652bc65c9108; original global index 15156.
def localCycle00563 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 30 1, .triangle 34 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle c2ca707c82cf743a02c8e309cd66caebe4c27dabcbfab2b38211db62bcf7927e; original global index 15200.
def localCycle00564 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 4 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 23 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle c2cf3177a1cabf8ceb906ca253abc56db320e564398c9f891d87c4f0ba37531a; original global index 15202.
def localCycle00565 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Original cycle c2e03c3413bd927858d70170afb33006f207acb6b1a2770ace1026855766afe5; original global index 15206.
def localCycle00566 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .gapLower 6 4, .triangle 4 1, .triangle 23 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle c36753380a3cb483feaded71f2f958f58eeacf5ea10cc948244f83e42806cbd3; original global index 15247.
def localCycle00567 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 4, .distance 0 5, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .theta 0]
    constant := ![2, 0, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.gapLower 0 6, .triangle 2 2, .triangle 12 2, .gapLower 0 3, .triangle 13 1, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0]

-- Original cycle c3a8f13de9694edfdba11018d0bbd97d6b39b87205c5c195e11e5251cb418903; original global index 15271.
def localCycle00568 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 5 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 14 2, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle c3f5a42ac157786c4bcac543c8c596a72c74773533ad7fb2989e1c1d9c7531b8; original global index 15284.
def localCycle00569 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 12 0, .gapLower 0 2, .triangle 5 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle c45710ba464254eed41ec402b7aaa2679f35c7baba449adb59abdf2fafef5f8a; original global index 15316.
def localCycle00570 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle c47ef92f03fb651544e3712d93545f984474cb91c87312c6ed6c2b89c6ac39c0; original global index 15323.
def localCycle00571 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![4, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 28 0, .triangle 29 0, .triangle 23 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle c493dade3da3d2a4b41494dd02e9edca3b21d6fca316117d71f0173b4d3860e4; original global index 15329.
def localCycle00572 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -2, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 27 2, .gapLower 6 4, .triangle 13 1, .triangle 23 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle c5a8753f03fb235f369a4780103b5f447f81ee483731addc4b4865903fc26ecb; original global index 15417.
def localCycle00573 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 8 2, .triangle 14 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle c5ba336d0ea29dbc647ae7820958c5b54e5b97fd7dfd3d74398c821f1e3c7215; original global index 15421.
def localCycle00574 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 0 6, .distance 4 6, .distance 1 6, .distance 1 2, .theta 1]
    constant := ![3, -2, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .triangle 12 2, .gapLower 0 3, .triangle 13 1, .triangle 23 2, .triangle 18 1, .corridorLower 1 2]

-- Original cycle c63f6f2c1ab9dd153c82553524990e5ee9819a9a5eb2dfc924f19d5d9c799a07; original global index 15459.
def localCycle00575 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .gapLower 6 2, .gapLower 6 1, .corridorLower 1 6, .thetaLower 1]

-- Original cycle c78bac65f37bd04225c4afe9506fecff425940efb08db3f38a7e509bf166b042; original global index 15574.
def localCycle00576 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 4, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .theta 0]
    constant := ![2, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.gapLower 0 6, .triangle 2 2, .gapLower 0 4, .triangle 13 1, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0]

-- Original cycle c8361b88013dbefe2e409ca810ee8915ffd73a14489cd88839bdd5300788c6e5; original global index 15626.
def localCycle00577 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle c85a42e4c1425a7af2ed56f62c79490fb2b7ec0a95cba9241ebc4f56d0763294; original global index 15641.
def localCycle00578 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 8 2, .triangle 14 1, .triangle 24 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle c96f5e1056774a31be68084dab072254750f7b1f038ef7e8a7825a648a19f27a; original global index 15747.
def localCycle00579 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle c9e1eddf3a1c1afe986321124568a252470228c29b7b69fd778351cbd145b04c; original global index 15778.
def localCycle00580 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 2, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 1, 0, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 1, .triangle 30 0, .triangle 26 1, .triangle 5 0, .triangle 0 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle ca511c8be7fd56a99fb7f934517e1b96f010d87529ff4bb171eb0f2f2de4dd70; original global index 15813.
def localCycle00581 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 8 2, .triangle 14 1, .triangle 24 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle ca8a061bbed47eb5c653e74878c9b7064402c1f33f335bb5d3e4fc127689a276; original global index 15829.
def localCycle00582 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 1, .gapUpper 5 1]

-- Original cycle cbf7975db24af46033f1e1915be25d12d6e4b56d0f7734da5cf9eade58c69b1b; original global index 15937.
def localCycle00583 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -2, 2, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 2, .gapLower 6 0, .gapLower 6 6, .triangle 33 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2]

-- Original cycle cc1f5319d62e16e457af91b8891d0c6fa99df9d2040025c75cf671ef108c67ca; original global index 15954.
def localCycle00584 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle cc27b7ed29267f830f24eb89d9bddbcb68bfc0976e5696d2d4b1b64a325096f5; original global index 15957.
def localCycle00585 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 13 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle cd8b4d45072c5f36c55e5a306d46c02dda2a951d66f4784c8ad0b9ccf4fe2dee; original global index 16063.
def localCycle00586 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, -1, -3, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 33 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2]

-- Original cycle cda6c428ddacb5c815b689eab66e7cc5c7a15581a756c543edeebecd2ef182f1; original global index 16073.
def localCycle00587 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .triangle 13 1, .triangle 23 2, .gapLower 6 0]

-- Original cycle ce53558d2a83c2f8cc7c35318ee191913e0298b5e8640bbeca339ae4fe3aab98; original global index 16118.
def localCycle00588 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle ce5d4f46d8551b8c881ef28b97aa8946b6521ec6e432b5efd7ade475b395adc3; original global index 16122.
def localCycle00589 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 23 0, .gapLower 4 0]

-- Original cycle ce938c55adebddcb03c92dcd3533ec92192a827ccc8db1126d7c76bb15885dac; original global index 16133.
def localCycle00590 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 5 6]

-- Original cycle cfb8e2544ec97e0ea43942dc5b696a695f44cd3a6e3cb7e4954e763be5d23a97; original global index 16211.
def localCycle00591 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 3 6, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 5, .gapLower 6 4, .triangle 32 1]

-- Original cycle d01de4380e0bf23ffab60b18d1b5247ef4570aa01aa92c10420953c489621f64; original global index 16245.
def localCycle00592 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 2, .triangle 30 0, .triangle 24 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle d0ae5b0e2c3d76869abcd9ef4af2b733bcc225b9b5c3f0f308efa1b93d88333e; original global index 16285.
def localCycle00593 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 6, .distance 0 5, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, 0, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 2, .gapLower 0 4, .gapLower 5 1, .triangle 22 1, .gapLower 4 0]

-- Original cycle d0e2e8892059b78b40d16df614635627c43994765d2670056af54a577cb72b88; original global index 16309.
def localCycle00594 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 18 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle d116ef1356192fe48cdc0238a19ccecb222ece7249f123ed95e7bf28c005dc1b; original global index 16327.
def localCycle00595 : Cycle where
  length := 12
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 5, .distance 1 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 4, .theta 0]
    constant := ![2, -2, 0, -1, -1, 0, 3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .gapLower 5 2, .triangle 24 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 13 0, .corridorLower 0 4]

-- Original cycle d14103bc565b90665b82b2ff4fa1c7197860f9ea273d3eb1a7af61811ada59a3; original global index 16334.
def localCycle00596 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 6, .distance 0 5, .distance 4 5, .distance 1 5, .distance 1 2, .theta 1]
    constant := ![3, -2, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .triangle 13 2, .gapLower 0 3, .gapLower 5 2, .triangle 22 2, .triangle 17 1, .corridorLower 1 2]

-- Original cycle d158b39bde4b5a30be7918012ca0cc842ba5fd4faf99b8956f651ab3a51c006b; original global index 16342.
def localCycle00597 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle d19693f9829e00c1c39620a248c6acde6c494cb8e955feb57cc334f68d25bfac; original global index 16357.
def localCycle00598 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -1, -3, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .gapUpper 2 6, .thetaLower 2]

-- Original cycle d20112bfeda6ad36064ba95b9601cbcfa5ae20e9865b40b3c9bef689bcf5c621; original global index 16390.
def localCycle00599 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 4 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 13 2, .gapLower 6 1, .corridorLower 1 6, .thetaLower 1]

-- Original cycle d2bb87d4c88ffada8f6222b45d59e32f8fc61e4284959dad2bab80b96a561ce5; original global index 16445.
def localCycle00600 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .triangle 14 1, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle d32cae771064c5cd1d0fb8621fd98956496f4013c39a812353f2d93263e4d99d; original global index 16473.
def localCycle00601 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle d3a5da679f14bb37da2217a874478ac579b09633e5ac97141cb3d672abf06185; original global index 16512.
def localCycle00602 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, 0, -3, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .gapLower 6 2, .triangle 4 1, .triangle 23 1, .triangle 22 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle d3db8e01e6380e2915ea236ebe2bfe9cb13d575621db7b13812215bf4e5e1602; original global index 16537.
def localCycle00603 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d4436985a95edc7f5998a9b39c349142b9ebc7cf68401ed651d5bfc50c1e1da2; original global index 16563.
def localCycle00604 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 26 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle d4918aee3d8fe0cc7478878748b6268842ae2a258c84a4cb080abe819bb0ffef; original global index 16585.
def localCycle00605 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle d4c1fc29fdc10752e664050d5c9cf66590a164b8ba597bb630867210c8f9ca93; original global index 16598.
def localCycle00606 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, 0, 0, -3, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 12 2, .gapLower 0 3, .triangle 13 1, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3]

-- Original cycle d50ae767844836dd9ff63fa05a69036ea6972185cee7cb7517dbee23dd9454bb; original global index 16623.
def localCycle00607 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 5, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .gapLower 5 3, .gapLower 0 4, .triangle 4 1, .triangle 24 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d55cd286a834e5dc7deb1c7c9b008300ffeea3987df4fbba9b3754646a420b69; original global index 16651.
def localCycle00608 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 5 6, .distance 2 5, .distance 2 3]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 30 0, .gapLower 2 3]

-- Original cycle d5c14750c49baee079d8c1a45e9454694b4de6922006a516f1ae2c89498a73d2; original global index 16685.
def localCycle00609 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 5 6, .theta 6, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, -1, 0, -2, -2, 0, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2]

-- Original cycle d5e793060685d718bd7b203f484a7de3df165695c4632b452da2aa9491f0b8a5; original global index 16694.
def localCycle00610 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 23 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle d5f6e6370af3bf19bdd1ee75be4e8c2b99bcf153da5ce7ad330468d6ea6fe888; original global index 16698.
def localCycle00611 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 4 1, .triangle 23 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle d641f8634ae2d90fd765c5868bde04423d7615397202a9dacbd3c7e06aef81ec; original global index 16726.
def localCycle00612 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 8 2, .triangle 13 1, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle d6a8b2f2c0291a720414d76c20da066ea9176e32047bb9eec3dccc8588fcabb9; original global index 16755.
def localCycle00613 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 14 2, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle d73e5ec5d1d160eff8e6fb4c110a687f39270640953a424fb1656df0807fd6b5; original global index 16798.
def localCycle00614 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 0 6, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 2 2, .triangle 8 2, .gapLower 0 2, .gapLower 0 1]

-- Original cycle d751872b8e0f1f402710c704ec3500084189570bfdf76c5c8b030472822cd0bd; original global index 16804.
def localCycle00615 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .gapLower 6 4, .triangle 13 2, .triangle 14 1, .triangle 24 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle d7dfa60378e605409883fe04875162879d3fd246639f94a69b2a940988f4aa3c; original global index 16844.
def localCycle00616 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Original cycle d804111076fe253171abb9673373bc959d1407a2e206766437f92032055b1b71; original global index 16860.
def localCycle00617 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 5, .distance 0 4, .theta 0, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, -1, 2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 1, -1, 0]
    strict := ![false, false, true, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 2, .gapLower 0 3, .corridorLower 0 4, .gapLower 0 6, .gapUpper 1 6, .thetaLower 1]

-- Original cycle d81df5cbc1cf9241d36bad843ddbc094d0476ec3759fc9e9ddc7a44112c4ffcc; original global index 16869.
def localCycle00618 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 4 1, .gapUpper 1 5]

-- Original cycle d8a473c3e73a55ac1a90ca3da7a0c92a022d567a21eb0a76fbe19e3e00249f99; original global index 16910.
def localCycle00619 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 5 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 30 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle d907d6b4ac0e8270719bd47b7e3fba4e5fb3995a768ec735ef61d271a83cc6ae; original global index 16952.
def localCycle00620 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 13 0, .triangle 2 1, .triangle 22 0, .corridorLower 4 5]

-- Original cycle d90c1b65969b5333abf9353b6f826d9819bb79e38fe1eb4444ae0170c5e4843d; original global index 16954.
def localCycle00621 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -1, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle d92fd58ec59e4fa894e532e563e39c6f92dce48eccc582ac21a0912c12bc9e1b; original global index 16969.
def localCycle00622 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 8 2, .triangle 13 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle d968ce755921935b9cc54945147d06d7ddd261ad747ed0f0e7e70eacb35a5dfe; original global index 16992.
def localCycle00623 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle da3aa0c4cdb0a8c2a75c68e3ea1233c53240a6a0d491ebae20a1dcdd4be02d36; original global index 17051.
def localCycle00624 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle db2e9feb633fd0c79946a6e23d54802743d3c4d2e75d4a0d3cb3bc40500f94d5; original global index 17129.
def localCycle00625 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 4 6, .theta 4, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 21 2, .gapLower 6 1, .corridorLower 4 6, .thetaLower 4]

-- Original cycle db4a7074999cf5f9db86f0c160e1e53714753bec37a94ed232eef39ff50da394; original global index 17142.
def localCycle00626 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 6, .distance 0 4, .theta 0, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -2, -1, 2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 1, -1, 0]
    strict := ![false, false, false, false, true, true, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 13 2, .gapLower 0 3, .corridorLower 0 4, .gapLower 0 6, .gapUpper 1 6, .thetaLower 1]

-- Original cycle db6e862505d013e6ca48fa982fc84e879403576e7202bf42dd868e6505568cb7; original global index 17150.
def localCycle00627 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 2 2, .gapLower 3 2, .gapLower 0 1]

-- Original cycle dc04151c255f5e963a12de3afbf5188f325eebb29798c219fdea9b7ab1e4e796; original global index 17198.
def localCycle00628 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 4, .triangle 14 1, .gapUpper 5 2]

-- Original cycle dc58060320ac95b45bdeb3dfe3d231c21db436944aee6b0e3bf113ac7c451e8a; original global index 17220.
def localCycle00629 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle dc71ad886bb99e53346125279377e71c2eaa9d4e4332adb9eb04951f34594b58; original global index 17227.
def localCycle00630 : Cycle where
  length := 4
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 6, .distance 0 5, .theta 0]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 4 2, .gapLower 0 4, .corridorLower 0 5]

-- Original cycle dc9ef6c70ab89c35abb224db2079c0d7b28d8c0040b6f7b9517b7b1f0af379ce; original global index 17236.
def localCycle00631 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 2 6, .distance 2 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 3, .gapLower 6 4, .triangle 29 1]

-- Original cycle dce863df8a4c0a589650274fb0fa112bf0125769b4949406286f07860bc8eaf6; original global index 17266.
def localCycle00632 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 29 1, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle dd00edd1b89d9677f41d56fd745198372496678590274c5f3778cd1708d1d3f1; original global index 17277.
def localCycle00633 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 4 1, .gapLower 6 2, .triangle 24 0, .gapLower 1 3]

-- Original cycle dd7ae4d560f023bbc449fda94c8b57184c511f1955d6d369122afb608823a32c; original global index 17314.
def localCycle00634 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 8 2, .triangle 13 1, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle de03c066643bb4f7b87e0c0c4e952dfb45483b0640255cb20260b63a687ad3f1; original global index 17360.
def localCycle00635 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 5 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle de5c7b90255e159d70045a774070416a5fdcd8460c519a8485015d5de137c54f; original global index 17382.
def localCycle00636 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .gapLower 5 2, .gapLower 0 3, .triangle 6 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle de971f97a2f2f3a033ef2cf623be98265dc315eb998793858da3bf96929e4088; original global index 17407.
def localCycle00637 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 2 6, .distance 4 6, .distance 2 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 29 2, .gapLower 6 3, .gapUpper 4 4]

-- Original cycle decb2ba446b16b917ac4ba41200d574a3ae75240004ad42c42ad82638e22dd3f; original global index 17420.
def localCycle00638 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 1, .corridorLower 1 6, .thetaLower 1]

-- Original cycle dee95455ad1b96e7dec7e71275661f823013ce8e4d7382cc709362b72ef7a284; original global index 17427.
def localCycle00639 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 5 6, .distance 0 6, .distance 1 6, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .triangle 14 2, .gapLower 6 1, .triangle 23 1, .gapLower 4 0]

-- Original cycle def7a1109669adf1aa5cc8d2d73d1816f74402c8511db3b4843116462f0301c9; original global index 17432.
def localCycle00640 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 13 1, .triangle 23 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle df6a216ec0346fe2036f7bcc41de979a13959cda1fa06a402840db268f1d84a1; original global index 17457.
def localCycle00641 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 12 0, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 2, .thetaLower 0]

-- Original cycle dfbad6c18ee0cc613e037350f615ab015b92e2ca8c2e7173bb5f60b378673eef; original global index 17478.
def localCycle00642 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle dfd71832e5b0169e3597e84eb7c7981817cbf6bd11ae621a317728e92d4c9ba2; original global index 17493.
def localCycle00643 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .gapLower 6 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle e00e39183b393243b1450754d6ceae83ef7fbb3cabd9fa9b5587c582d37d8672; original global index 17515.
def localCycle00644 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle e071bef657dbf8894e1a992ba1d3ff3d78a708b183b0ca32dbdfcbf4bdba47b6; original global index 17549.
def localCycle00645 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle e0826e74a66a831343699ac16d3b8043808d7b41db5ec69cfbbd0dfe6f87d572; original global index 17557.
def localCycle00646 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle e0d8322bdf84aa29c74a2874f1f034b0688476c87851de549852bafc614f47c0; original global index 17579.
def localCycle00647 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 4, .triangle 13 1, .gapUpper 4 3]

-- Original cycle e1877c2f30194176760356261f246b5a82e3ab1a0eb2e6209940ade408e06ee1; original global index 17638.
def localCycle00648 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .theta 0, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -2, -1, 2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 1, -1, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 14 0, .gapLower 0 2, .corridorLower 0 3, .gapLower 0 6, .gapUpper 1 6, .thetaLower 1]

-- Original cycle e1ce91f1720c1a4ae911636f045300c4d9f7c11843023c6c34d4b5662e9df220; original global index 17657.
def localCycle00649 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .gapLower 6 1, .corridorLower 1 6, .thetaLower 1]

-- Original cycle e212f83718d8d71f4fa0f75e2a9e701b7e097f83eeedcfb9c0a064fdbdad545c; original global index 17677.
def localCycle00650 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 3, .triangle 23 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle e251072bffe31c92a299762489a27da8640d2e70ff1f3df4eeda075267052045; original global index 17696.
def localCycle00651 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .triangle 22 0, .gapLower 4 0]

-- Original cycle e2650ee67f69cdb056645f1641235249fcd84b76b4529a2d582e6557be293038; original global index 17701.
def localCycle00652 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 2, .gapLower 6 5, .triangle 8 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle e29db16197af46f6d31d904b9d02bc091bbf5cf2dd27a2af0429f09262591057; original global index 17722.
def localCycle00653 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 8 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle e3222235f0f988abdaa1432edd561bcd39a7641bf74a99ad9c6de578047d7faf; original global index 17764.
def localCycle00654 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 2 6, .distance 4 6, .distance 2 4]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 29 2, .gapLower 6 3, .gapUpper 4 4]

-- Original cycle e3bdd344bc8fbf044613b1293bf45ca59b2b0b5e9581f89dfb1d18639972498a; original global index 17814.
def localCycle00655 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -2, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .triangle 27 2, .gapLower 6 2, .gapLower 6 1, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle e42de115c8019061100509d3bfe95fa884b2c05baf09cd1d9ed7403413e42654; original global index 17842.
def localCycle00656 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 14 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle e431a8c3a1e4dac33c4165284d63e5d99faad8c99da03d1321dd3cb5074f8d66; original global index 17844.
def localCycle00657 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle e46bfb4a6a0b1f3ab78af6da5efba35dcbda4dfcd0e386b8e7db8466dd69622c; original global index 17855.
def localCycle00658 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 23 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle e4abe7966e5335653492190850299b76e0048e1e9d34a7e077041118ad16aaa7; original global index 17878.
def localCycle00659 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 4 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, -3, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 29 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle e4d5b2ad5066aa7f6b2a0199839ff68c4d5ec13fa1908e8b34c753103522b0fa; original global index 17888.
def localCycle00660 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .gapLower 6 1, .corridorLower 1 6, .thetaLower 1]

-- Original cycle e5096ed2825c0b40b4cb47a6d7456543770639a547c2af503dd6be18c907ad14; original global index 17905.
def localCycle00661 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle e5164348e0a2c62e39ddb33af1d68ebe4e4d416274a1883afb82f14ac530b965; original global index 17908.
def localCycle00662 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle e53cc835a49c121df6161543ad698d79dced1e439bdb58e868b971de631cfd3a; original global index 17919.
def localCycle00663 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle e545de3c729a9107f5eec78bd656cc9a21c311d132c73caad1abcfa495d04567; original global index 17923.
def localCycle00664 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, 0, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 27 2, .gapLower 6 4, .triangle 4 1, .triangle 23 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle e5cbab2008e8c2efbc93876022c9d50e42930e1b72a2f4cb87ab85630972c312; original global index 17979.
def localCycle00665 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapLower 6 2, .triangle 13 1, .triangle 9 1, .triangle 5 1, .corridorLower 0 2, .thetaLower 0]

-- Original cycle e5f72892a1667f11ff99bd8bd67ad3538f403d039b4f56a1748b67280299aa06; original global index 17993.
def localCycle00666 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 6, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -2, -2, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.triangle 3 2, .triangle 14 2, .gapLower 6 2, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle e5f87bd87a193df81600d7bc90cc01757bb9c5b6c6ea15d17da5a2cb97fc1fbd; original global index 17994.
def localCycle00667 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 4, .theta 4]
    constant := ![3, -1, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .gapLower 6 2, .triangle 4 1, .triangle 23 1, .gapLower 4 0]

-- Original cycle e5f9bc627c20203ba4bc4babe15c756ace3003c32f6b86e9d4e7cb03470a6c3a; original global index 17995.
def localCycle00668 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle e6452bec323d746aba338c4472a02df17a4aa7e366581539f651fdcfb9a29506; original global index 18017.
def localCycle00669 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .gapLower 6 4, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle e6c10f23cc7ebe3de8e3cbe42c986c4d29ed30595a4588f870fa8bc092cb2298; original global index 18049.
def localCycle00670 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -2, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .gapLower 6 2, .gapLower 6 1, .triangle 23 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle e71a0bcd26d2a148b05afd83656104704c56f25bc07d4aa38d0f8aabe6d75e67; original global index 18076.
def localCycle00671 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle e759fe51c4ec9c28593a21743be1a025aee351665dde537eec4c803890cef56f; original global index 18096.
def localCycle00672 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle e92136fcae60dade4d490859ccf5fbbac45b17206cc4aa8a613ce55b3595c6bc; original global index 18218.
def localCycle00673 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 2 6, .distance 5 6, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 30 2, .gapLower 6 3, .gapUpper 5 3]

-- Original cycle e9266149818abe3de1024157f08e187103953a467aa6af0a68f342e30c81044f; original global index 18219.
def localCycle00674 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 14 2, .gapLower 6 2, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0, .thetaLower 0]

-- Original cycle ea13b51f3d33d7298e75971d87b2f18bf138736496c98f12969f5f0bad468cdd; original global index 18287.
def localCycle00675 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle eaa35a0ca640e8e7f5b8566f5ee3a5d722f52c4d80823ef03512c336c0375152; original global index 18325.
def localCycle00676 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle ead79f953eb9d3f8c6729a23c5f3999f41725a7fd82e32549248c207c931d1f7; original global index 18344.
def localCycle00677 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 1 5, .distance 0 1]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 5, .gapLower 5 2, .gapUpper 1 5]

-- Original cycle eadf85f0e65ef2f5b451a5512a6a695de4e7c791b3e070695015ef9842e6d814; original global index 18346.
def localCycle00678 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 13 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle ebc60f4634d94da16807128b55a8917de683e6329b75f16319faa54daee3568a; original global index 18396.
def localCycle00679 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, 0, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 3, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle ebe7aae66c8768b4cdcf800193137fe7306ff1ca7669974f6208edec375c1336; original global index 18413.
def localCycle00680 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, -1, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 13 2, .triangle 14 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle ec73fad42ad241489157b0d7cd8065cf4ec7058a5fa055e3d2903f20d2060690; original global index 18454.
def localCycle00681 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 4 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, -2, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .gapUpper 2 6, .thetaLower 2]

-- Original cycle ec758505c1dad9a3f06f68240f4bd933f33a845fdcdf4ab03a22af4748bdbfe6; original global index 18456.
def localCycle00682 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle ecf6ddb9936bc7d7d7078b04e87c6983a221aeb60d667fc9ea9b1a472a8c22e9; original global index 18497.
def localCycle00683 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 14 2, .gapLower 6 2, .gapUpper 5 2]

-- Original cycle ed77e966dfb64c8194aa2b5d10bb19fb2d47d94ee73c836dab79345d2fc7d5d7; original global index 18536.
def localCycle00684 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle edb9f6e144deb0b39f26f2b5e1068095b79a1b3d0bb940266ee10747f6fd5509; original global index 18561.
def localCycle00685 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0]
    constant := ![2, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.gapLower 0 6, .triangle 2 2, .triangle 13 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0]

-- Original cycle edc853e2dd6f3f7b0712ed04dfc93de8fc380e9e505496ed90dd3b6a52d863ed; original global index 18566.
def localCycle00686 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 12 0, .gapLower 0 2, .triangle 5 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle ee0037110575978a16f10bfd2c854fd7b325abb4555c1e356f56e90765a49812; original global index 18581.
def localCycle00687 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle ee148a50eeaa8e8a608601f414aa5266ea9916dda385eba5011656ceee2179a5; original global index 18586.
def localCycle00688 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .theta 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 1 2, .theta 1]
    constant := ![3, -1, -1, -2, 2, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .gapLower 6 0, .gapLower 6 6, .triangle 27 0, .triangle 5 0, .triangle 0 1, .corridorLower 1 2]

-- Original cycle ee2ad24b9069e126f383c2e1dfc03694c80880ef82920d8330ff4d75775441ec; original global index 18589.
def localCycle00689 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 8 2, .triangle 13 1, .triangle 23 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle ee93153f83fcb29d66df39a07c79de3e96ce605ce26f623d03974ab95a1ced67; original global index 18619.
def localCycle00690 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 0 6, .distance 0 3, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 12 2, .gapLower 0 3, .gapLower 0 2, .gapLower 3 1, .triangle 15 1, .corridorLower 1 2]

-- Original cycle eec368cb986b12e45734b36cecc39d12bb68face6810687d66c1a9595249950a; original global index 18634.
def localCycle00691 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, -1, -1, -2, 2, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .gapLower 6 0, .gapLower 6 6, .triangle 33 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2]

-- Original cycle ef6a8dcc8e97edb36e6fd545fbc59a2fa590874fc4eefd3b340c1823846ecd18; original global index 18681.
def localCycle00692 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![-1, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.triangle 13 0, .gapLower 6 2, .gapUpper 5 2, .triangle 12 1]

-- Original cycle efca9242784cc74d108434af22f820ecdf46a879d766dfd0a62f6aac873f6e77; original global index 18709.
def localCycle00693 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 4 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 13 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle f06b47b200b60ffb72e88b7d6677cb6651de85a3984c979be77908fa8c5a7d35; original global index 18747.
def localCycle00694 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 8 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle f08ecc2e7cf1060e4e0244cb46bd1466402d258e4654abe08ac51c9806e0b30e; original global index 18756.
def localCycle00695 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 24 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle f09a2e0b7c54f7147c3c7d4a818fe001cbaa7c695bcd4c94a556f7e5de3b5cc2; original global index 18760.
def localCycle00696 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 2, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle f09ab7cfc20c7cea21cba27355717fdd75fa222b9808199d1ed916c780f363df; original global index 18761.
def localCycle00697 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle f09fa60f050f09792859054cd7dbfbd991677d29521eee69385bdc67d47ae384; original global index 18764.
def localCycle00698 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle f113eca9a4eef6ee5cda66b2debf7e33b0b2c5f4e0205434f6ee5e50ef693f1f; original global index 18804.
def localCycle00699 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle f1c75bd6200a170fe0a5d5e985da8999acb780b386596b17ec9f6dfe76c48a0a; original global index 18854.
def localCycle00700 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 0 5, .distance 0 4, .theta 0, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -2, -1, 2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .gapLower 5 2, .gapLower 0 3, .corridorLower 0 4, .gapLower 0 6, .gapUpper 1 6, .thetaLower 1]

-- Original cycle f1e58cca1a09a4bc8a76f8a1c0fa28893e7a6b5bca4985675ebddbabd13527ea; original global index 18863.
def localCycle00701 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 12 0, .triangle 6 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle f2057c72f049f244768f7ce918c817044e949ac21cd63de4de1687fd47376394; original global index 18873.
def localCycle00702 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 8 2, .triangle 13 1, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle f208a9a8e9c8e25551ef11605061bedc7287048e33758342b3fdf6451eb412b0; original global index 18876.
def localCycle00703 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 5 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -3, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 30 2, .gapUpper 2 6, .thetaLower 2]

-- Original cycle f2250f6c7991ac0423aadce80670ff1d3ef65e63add0b47d2d32ed265f78eb89; original global index 18882.
def localCycle00704 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle f25f596389d10f2e351b3eb5e5dfb59f0e4e13051e32cc2ed8b685ca4a8b82fa; original global index 18901.
def localCycle00705 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 3, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .gapLower 6 4, .triangle 14 1, .triangle 24 0, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0, .thetaLower 0]

-- Original cycle f2fe3af6504c471bf1262a783061b24dc5f3a8fa4bf76defa8260bc4a1603ec1; original global index 18942.
def localCycle00706 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 2, .triangle 12 0, .triangle 34 2, .gapLower 6 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle f351dde22b53cc68bc57b12cb3ad65213159cf9857cf0994eb4d1ee261dde33d; original global index 18977.
def localCycle00707 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 24 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle f3abc699a30265fa8783dc12190688ccbe8d1a1519e0f390b255c3a2de02859d; original global index 19008.
def localCycle00708 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -3, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 2 2, .triangle 13 0, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle f3c2f391f136af1cf3d2fc20566d00e7cc684fbe2d2d2460093f7257de859af4; original global index 19014.
def localCycle00709 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle f3c6220ee036775892337abe467cd79d149724c01f62562a2d7ccb7dd0009f90; original global index 19016.
def localCycle00710 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle f41b5b9fda1d3a9964541ec8fc0d126e58661007e8848cf4a0162a70109d3331; original global index 19034.
def localCycle00711 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 31 1, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle f47344f946975eee64b92a4d91740b26dec771bd24a756a4f48de245e1ca262f; original global index 19060.
def localCycle00712 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .gapLower 6 3, .triangle 24 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle f5a19877ace4aaacfc54610fd04ab33e46ae194877b7e7566b74faff9105df74; original global index 19152.
def localCycle00713 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .gapLower 6 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle f68e06cdf9e9ba7c3943311a1929244225083d05f6886cca33241719b0a8f466; original global index 19236.
def localCycle00714 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 4 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 34 1, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle f6a1149cb68673001c651af68ac67f32a9960146ae9d1a8e8c1825b91492b2f1; original global index 19243.
def localCycle00715 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 5 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 30 1, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle f6be143f600dc198c1cedb182796ec692265e437c5dc492d8d12b1ea2cf2ec26; original global index 19250.
def localCycle00716 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 0 6, .distance 0 4]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 4 2, .triangle 13 2, .gapLower 0 3]

-- Original cycle f6d7e776a3837fff6ee313a7219ffc190400e21f21cc3e6aca7e216749cdc762; original global index 19253.
def localCycle00717 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 3 2, .triangle 32 1, .triangle 13 0, .gapLower 0 2]

-- Original cycle f72c00c826617c8ac156a798dbbc68dede43b285eba830807ee0c9c64d8eef86; original global index 19275.
def localCycle00718 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 3, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle f78f4f9e5c794a8c770f819b510fba4cea146f171c63b641e27ffd7388bc18c9; original global index 19306.
def localCycle00719 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, 0, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 27 2, .triangle 8 2, .gapLower 6 3, .triangle 23 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle f7fbeafbb8efb46b3e6c04c3f06eea00bd0bfb0cf6f93a20c842907e442796f8; original global index 19330.
def localCycle00720 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 5 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -2, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .gapUpper 2 6, .thetaLower 2]

-- Original cycle f851fc25243fffb92d44064c940c94701bac3efd500314f53e76b28af26b7acf; original global index 19369.
def localCycle00721 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .gapLower 6 4, .triangle 8 2, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle f8aa82729107671c1bfd3110076f5678b4eb0f30deb04db21c98997ad04c65a2; original global index 19392.
def localCycle00722 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 0, .triangle 24 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle f8bc6237ef643d60c2af354bcdaa8091596c69d9f2e09554628a2c4c1d595634; original global index 19399.
def localCycle00723 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, -1, 0, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .gapLower 6 3, .gapLower 6 2, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle f8cfd4e8f5ba2d13ac0c5aabbce3dd1403496ce965c11aab9a1dd95479e1fa6f; original global index 19407.
def localCycle00724 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle fae187be62870b96a6b8944492a6c34e0cd0753691921fd73ed46e7257750683; original global index 19578.
def localCycle00725 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .triangle 8 2, .gapLower 6 2, .triangle 23 2, .gapLower 6 0]

-- Original cycle fb121b2d3a3d40b2d84d6b8d2e5f997adc26b40fd865b99ecce0bea504732496; original global index 19596.
def localCycle00726 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .gapLower 6 4, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle fb5613d6b4944daf75dbe8649f5cae2a83ddd17aabdbfde29a1dfbe68355c610; original global index 19615.
def localCycle00727 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle fb670fde311731345087dc0ca3ff46d5441e218dc2edda08c0adb029dcb781fa; original global index 19624.
def localCycle00728 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle fbd17858422e3657e33cac94bef95dea819d65bdfc30a77d3b2d1e7d14f607c2; original global index 19659.
def localCycle00729 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 13 1, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle fc340767ad742ee3635f7ffe1b6f9d974c77b431e453ee7e7da1d48bffcedb6b; original global index 19697.
def localCycle00730 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -2, 0, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true, true, true, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 2, .triangle 30 0, .triangle 14 2, .gapLower 6 1, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle fc4e1162d4f33a3c95193a53d3d0d449eb389c6c106b42f0cfb26c66d8f665e3; original global index 19707.
def localCycle00731 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 12 0, .gapLower 0 2, .triangle 5 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle fc4efce37cacb96bb38b2d2649896c3096c49b0ae7e750527d261a1785fce7b0; original global index 19708.
def localCycle00732 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![4, -2, 0, -2, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .gapLower 6 4, .triangle 27 2, .gapLower 6 2, .triangle 4 1, .triangle 23 1, .triangle 22 0, .corridorLower 4 5]

-- Original cycle fc6fdb5a92e01e49fe99ab84b067d71996bbc8ef4d144bff5d58fe3f4782f417; original global index 19722.
def localCycle00733 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 0 6, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 14 2, .gapLower 0 3, .triangle 10 1, .triangle 5 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle fc87cd854bc4e902e736c4dee4f6a2d2a8f8bfd1186b9ce592519007298314f1; original global index 19728.
def localCycle00734 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 4, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 2, .triangle 13 2, .gapLower 6 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle fd3c317ad74558a40a7ef8670c5ea1175142e4dc4ddd7a2b0fea5aab1238b0d6; original global index 19791.
def localCycle00735 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 4 2, .triangle 34 1, .triangle 14 0, .gapLower 0 3]

-- Original cycle fe3a3d0089b05ec6c305ad5949265489f96e2b828d4e5d5d8ac07fe6e4321fa7; original global index 19871.
def localCycle00736 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .gapLower 6 4, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle fe8b40b2dd8934d1749bbc32e430730d56229e21fe5c07f459c27f5ecf35ce31; original global index 19899.
def localCycle00737 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 1, .corridorLower 1 6, .thetaLower 1]

-- Original cycle ff6e03fdc9105aa89eef350eef274b706fd4622f19830a0c4e3b1adaac14906d; original global index 19971.
def localCycle00738 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 5, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 2, .triangle 14 2, .gapLower 6 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle ff7684b7f6073b8082d32cdfa9665520d30de44eb21f702da58af3ad4b574d2d; original global index 19973.
def localCycle00739 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 0 5, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 7 2, .triangle 14 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle ff7f6f2a8acd862b79c32eca053e83f3cca82ba4414e3fcfbfac1733cb8e1f26; original global index 19977.
def localCycle00740 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 14 1, .triangle 24 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle ffb9e4e2f64a78843670dca930a9a9baafc45ebde1cfbb91f46e4be21fc38923; original global index 20001.
def localCycle00741 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 2 2, .gapLower 0 4, .gapLower 5 3, .triangle 22 2, .gapUpper 1 5]

-- Original cycle fffaa0b20eaf5fb35d4ab8761130cc23ddefce92751669e348eb58673eb39579; original global index 20023.
def localCycle00742 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6, .thetaNext 4]

def library : Library := fun id => if id < 371 then (if id < 185 then (if id < 92 then (if id < 46 then (if id < 23 then (if id < 11 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 8 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none))) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none))))) else (if id < 17 then (if id < 14 then (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none))) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)))) else (if id < 20 then (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none))) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)))))) else (if id < 34 then (if id < 28 then (if id < 25 then (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none)))) else (if id < 31 then (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none))) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none))))) else (if id < 40 then (if id < 37 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none)))) else (if id < 43 then (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none))) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))))))) else (if id < 69 then (if id < 57 then (if id < 51 then (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none)))) else (if id < 54 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none))) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none))))) else (if id < 63 then (if id < 60 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)))) else (if id < 66 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none))) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)))))) else (if id < 80 then (if id < 74 then (if id < 71 then (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)))) else (if id < 77 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none))) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none))))) else (if id < 86 then (if id < 83 then (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none))) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)))) else (if id < 89 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none))) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)))))))) else (if id < 138 then (if id < 115 then (if id < 103 then (if id < 97 then (if id < 94 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)))) else (if id < 100 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none))) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none))))) else (if id < 109 then (if id < 106 then (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none))) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)))) else (if id < 112 then (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none))) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none)))))) else (if id < 126 then (if id < 120 then (if id < 117 then (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)))) else (if id < 123 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none))) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none))))) else (if id < 132 then (if id < 129 then (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none))) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none)))) else (if id < 135 then (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none))) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none))))))) else (if id < 161 then (if id < 149 then (if id < 143 then (if id < 140 then (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none)))) else (if id < 146 then (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none))) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none))))) else (if id < 155 then (if id < 152 then (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none))) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none)))) else (if id < 158 then (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none))) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none)))))) else (if id < 173 then (if id < 167 then (if id < 164 then (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none))) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none)))) else (if id < 170 then (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none))) else (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none))))) else (if id < 179 then (if id < 176 then (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id = 175 then some localCycle00175 else none))) else (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id = 178 then some localCycle00178 else none)))) else (if id < 182 then (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none))) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none))))))))) else (if id < 278 then (if id < 231 then (if id < 208 then (if id < 196 then (if id < 190 then (if id < 187 then (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none)))) else (if id < 193 then (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none))) else (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none))))) else (if id < 202 then (if id < 199 then (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id = 198 then some localCycle00198 else none))) else (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none)))) else (if id < 205 then (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id = 204 then some localCycle00204 else none))) else (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none)))))) else (if id < 219 then (if id < 213 then (if id < 210 then (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none)) else (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id = 212 then some localCycle00212 else none)))) else (if id < 216 then (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none))) else (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id = 218 then some localCycle00218 else none))))) else (if id < 225 then (if id < 222 then (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id = 221 then some localCycle00221 else none))) else (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id = 224 then some localCycle00224 else none)))) else (if id < 228 then (if id < 226 then (if id = 225 then some localCycle00225 else none) else (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id = 227 then some localCycle00227 else none))) else (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id = 230 then some localCycle00230 else none))))))) else (if id < 254 then (if id < 242 then (if id < 236 then (if id < 233 then (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id = 232 then some localCycle00232 else none)) else (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id < 235 then (if id = 234 then some localCycle00234 else none) else (if id = 235 then some localCycle00235 else none)))) else (if id < 239 then (if id < 237 then (if id = 236 then some localCycle00236 else none) else (if id < 238 then (if id = 237 then some localCycle00237 else none) else (if id = 238 then some localCycle00238 else none))) else (if id < 240 then (if id = 239 then some localCycle00239 else none) else (if id < 241 then (if id = 240 then some localCycle00240 else none) else (if id = 241 then some localCycle00241 else none))))) else (if id < 248 then (if id < 245 then (if id < 243 then (if id = 242 then some localCycle00242 else none) else (if id < 244 then (if id = 243 then some localCycle00243 else none) else (if id = 244 then some localCycle00244 else none))) else (if id < 246 then (if id = 245 then some localCycle00245 else none) else (if id < 247 then (if id = 246 then some localCycle00246 else none) else (if id = 247 then some localCycle00247 else none)))) else (if id < 251 then (if id < 249 then (if id = 248 then some localCycle00248 else none) else (if id < 250 then (if id = 249 then some localCycle00249 else none) else (if id = 250 then some localCycle00250 else none))) else (if id < 252 then (if id = 251 then some localCycle00251 else none) else (if id < 253 then (if id = 252 then some localCycle00252 else none) else (if id = 253 then some localCycle00253 else none)))))) else (if id < 266 then (if id < 260 then (if id < 257 then (if id < 255 then (if id = 254 then some localCycle00254 else none) else (if id < 256 then (if id = 255 then some localCycle00255 else none) else (if id = 256 then some localCycle00256 else none))) else (if id < 258 then (if id = 257 then some localCycle00257 else none) else (if id < 259 then (if id = 258 then some localCycle00258 else none) else (if id = 259 then some localCycle00259 else none)))) else (if id < 263 then (if id < 261 then (if id = 260 then some localCycle00260 else none) else (if id < 262 then (if id = 261 then some localCycle00261 else none) else (if id = 262 then some localCycle00262 else none))) else (if id < 264 then (if id = 263 then some localCycle00263 else none) else (if id < 265 then (if id = 264 then some localCycle00264 else none) else (if id = 265 then some localCycle00265 else none))))) else (if id < 272 then (if id < 269 then (if id < 267 then (if id = 266 then some localCycle00266 else none) else (if id < 268 then (if id = 267 then some localCycle00267 else none) else (if id = 268 then some localCycle00268 else none))) else (if id < 270 then (if id = 269 then some localCycle00269 else none) else (if id < 271 then (if id = 270 then some localCycle00270 else none) else (if id = 271 then some localCycle00271 else none)))) else (if id < 275 then (if id < 273 then (if id = 272 then some localCycle00272 else none) else (if id < 274 then (if id = 273 then some localCycle00273 else none) else (if id = 274 then some localCycle00274 else none))) else (if id < 276 then (if id = 275 then some localCycle00275 else none) else (if id < 277 then (if id = 276 then some localCycle00276 else none) else (if id = 277 then some localCycle00277 else none)))))))) else (if id < 324 then (if id < 301 then (if id < 289 then (if id < 283 then (if id < 280 then (if id < 279 then (if id = 278 then some localCycle00278 else none) else (if id = 279 then some localCycle00279 else none)) else (if id < 281 then (if id = 280 then some localCycle00280 else none) else (if id < 282 then (if id = 281 then some localCycle00281 else none) else (if id = 282 then some localCycle00282 else none)))) else (if id < 286 then (if id < 284 then (if id = 283 then some localCycle00283 else none) else (if id < 285 then (if id = 284 then some localCycle00284 else none) else (if id = 285 then some localCycle00285 else none))) else (if id < 287 then (if id = 286 then some localCycle00286 else none) else (if id < 288 then (if id = 287 then some localCycle00287 else none) else (if id = 288 then some localCycle00288 else none))))) else (if id < 295 then (if id < 292 then (if id < 290 then (if id = 289 then some localCycle00289 else none) else (if id < 291 then (if id = 290 then some localCycle00290 else none) else (if id = 291 then some localCycle00291 else none))) else (if id < 293 then (if id = 292 then some localCycle00292 else none) else (if id < 294 then (if id = 293 then some localCycle00293 else none) else (if id = 294 then some localCycle00294 else none)))) else (if id < 298 then (if id < 296 then (if id = 295 then some localCycle00295 else none) else (if id < 297 then (if id = 296 then some localCycle00296 else none) else (if id = 297 then some localCycle00297 else none))) else (if id < 299 then (if id = 298 then some localCycle00298 else none) else (if id < 300 then (if id = 299 then some localCycle00299 else none) else (if id = 300 then some localCycle00300 else none)))))) else (if id < 312 then (if id < 306 then (if id < 303 then (if id < 302 then (if id = 301 then some localCycle00301 else none) else (if id = 302 then some localCycle00302 else none)) else (if id < 304 then (if id = 303 then some localCycle00303 else none) else (if id < 305 then (if id = 304 then some localCycle00304 else none) else (if id = 305 then some localCycle00305 else none)))) else (if id < 309 then (if id < 307 then (if id = 306 then some localCycle00306 else none) else (if id < 308 then (if id = 307 then some localCycle00307 else none) else (if id = 308 then some localCycle00308 else none))) else (if id < 310 then (if id = 309 then some localCycle00309 else none) else (if id < 311 then (if id = 310 then some localCycle00310 else none) else (if id = 311 then some localCycle00311 else none))))) else (if id < 318 then (if id < 315 then (if id < 313 then (if id = 312 then some localCycle00312 else none) else (if id < 314 then (if id = 313 then some localCycle00313 else none) else (if id = 314 then some localCycle00314 else none))) else (if id < 316 then (if id = 315 then some localCycle00315 else none) else (if id < 317 then (if id = 316 then some localCycle00316 else none) else (if id = 317 then some localCycle00317 else none)))) else (if id < 321 then (if id < 319 then (if id = 318 then some localCycle00318 else none) else (if id < 320 then (if id = 319 then some localCycle00319 else none) else (if id = 320 then some localCycle00320 else none))) else (if id < 322 then (if id = 321 then some localCycle00321 else none) else (if id < 323 then (if id = 322 then some localCycle00322 else none) else (if id = 323 then some localCycle00323 else none))))))) else (if id < 347 then (if id < 335 then (if id < 329 then (if id < 326 then (if id < 325 then (if id = 324 then some localCycle00324 else none) else (if id = 325 then some localCycle00325 else none)) else (if id < 327 then (if id = 326 then some localCycle00326 else none) else (if id < 328 then (if id = 327 then some localCycle00327 else none) else (if id = 328 then some localCycle00328 else none)))) else (if id < 332 then (if id < 330 then (if id = 329 then some localCycle00329 else none) else (if id < 331 then (if id = 330 then some localCycle00330 else none) else (if id = 331 then some localCycle00331 else none))) else (if id < 333 then (if id = 332 then some localCycle00332 else none) else (if id < 334 then (if id = 333 then some localCycle00333 else none) else (if id = 334 then some localCycle00334 else none))))) else (if id < 341 then (if id < 338 then (if id < 336 then (if id = 335 then some localCycle00335 else none) else (if id < 337 then (if id = 336 then some localCycle00336 else none) else (if id = 337 then some localCycle00337 else none))) else (if id < 339 then (if id = 338 then some localCycle00338 else none) else (if id < 340 then (if id = 339 then some localCycle00339 else none) else (if id = 340 then some localCycle00340 else none)))) else (if id < 344 then (if id < 342 then (if id = 341 then some localCycle00341 else none) else (if id < 343 then (if id = 342 then some localCycle00342 else none) else (if id = 343 then some localCycle00343 else none))) else (if id < 345 then (if id = 344 then some localCycle00344 else none) else (if id < 346 then (if id = 345 then some localCycle00345 else none) else (if id = 346 then some localCycle00346 else none)))))) else (if id < 359 then (if id < 353 then (if id < 350 then (if id < 348 then (if id = 347 then some localCycle00347 else none) else (if id < 349 then (if id = 348 then some localCycle00348 else none) else (if id = 349 then some localCycle00349 else none))) else (if id < 351 then (if id = 350 then some localCycle00350 else none) else (if id < 352 then (if id = 351 then some localCycle00351 else none) else (if id = 352 then some localCycle00352 else none)))) else (if id < 356 then (if id < 354 then (if id = 353 then some localCycle00353 else none) else (if id < 355 then (if id = 354 then some localCycle00354 else none) else (if id = 355 then some localCycle00355 else none))) else (if id < 357 then (if id = 356 then some localCycle00356 else none) else (if id < 358 then (if id = 357 then some localCycle00357 else none) else (if id = 358 then some localCycle00358 else none))))) else (if id < 365 then (if id < 362 then (if id < 360 then (if id = 359 then some localCycle00359 else none) else (if id < 361 then (if id = 360 then some localCycle00360 else none) else (if id = 361 then some localCycle00361 else none))) else (if id < 363 then (if id = 362 then some localCycle00362 else none) else (if id < 364 then (if id = 363 then some localCycle00363 else none) else (if id = 364 then some localCycle00364 else none)))) else (if id < 368 then (if id < 366 then (if id = 365 then some localCycle00365 else none) else (if id < 367 then (if id = 366 then some localCycle00366 else none) else (if id = 367 then some localCycle00367 else none))) else (if id < 369 then (if id = 368 then some localCycle00368 else none) else (if id < 370 then (if id = 369 then some localCycle00369 else none) else (if id = 370 then some localCycle00370 else none)))))))))) else (if id < 557 then (if id < 464 then (if id < 417 then (if id < 394 then (if id < 382 then (if id < 376 then (if id < 373 then (if id < 372 then (if id = 371 then some localCycle00371 else none) else (if id = 372 then some localCycle00372 else none)) else (if id < 374 then (if id = 373 then some localCycle00373 else none) else (if id < 375 then (if id = 374 then some localCycle00374 else none) else (if id = 375 then some localCycle00375 else none)))) else (if id < 379 then (if id < 377 then (if id = 376 then some localCycle00376 else none) else (if id < 378 then (if id = 377 then some localCycle00377 else none) else (if id = 378 then some localCycle00378 else none))) else (if id < 380 then (if id = 379 then some localCycle00379 else none) else (if id < 381 then (if id = 380 then some localCycle00380 else none) else (if id = 381 then some localCycle00381 else none))))) else (if id < 388 then (if id < 385 then (if id < 383 then (if id = 382 then some localCycle00382 else none) else (if id < 384 then (if id = 383 then some localCycle00383 else none) else (if id = 384 then some localCycle00384 else none))) else (if id < 386 then (if id = 385 then some localCycle00385 else none) else (if id < 387 then (if id = 386 then some localCycle00386 else none) else (if id = 387 then some localCycle00387 else none)))) else (if id < 391 then (if id < 389 then (if id = 388 then some localCycle00388 else none) else (if id < 390 then (if id = 389 then some localCycle00389 else none) else (if id = 390 then some localCycle00390 else none))) else (if id < 392 then (if id = 391 then some localCycle00391 else none) else (if id < 393 then (if id = 392 then some localCycle00392 else none) else (if id = 393 then some localCycle00393 else none)))))) else (if id < 405 then (if id < 399 then (if id < 396 then (if id < 395 then (if id = 394 then some localCycle00394 else none) else (if id = 395 then some localCycle00395 else none)) else (if id < 397 then (if id = 396 then some localCycle00396 else none) else (if id < 398 then (if id = 397 then some localCycle00397 else none) else (if id = 398 then some localCycle00398 else none)))) else (if id < 402 then (if id < 400 then (if id = 399 then some localCycle00399 else none) else (if id < 401 then (if id = 400 then some localCycle00400 else none) else (if id = 401 then some localCycle00401 else none))) else (if id < 403 then (if id = 402 then some localCycle00402 else none) else (if id < 404 then (if id = 403 then some localCycle00403 else none) else (if id = 404 then some localCycle00404 else none))))) else (if id < 411 then (if id < 408 then (if id < 406 then (if id = 405 then some localCycle00405 else none) else (if id < 407 then (if id = 406 then some localCycle00406 else none) else (if id = 407 then some localCycle00407 else none))) else (if id < 409 then (if id = 408 then some localCycle00408 else none) else (if id < 410 then (if id = 409 then some localCycle00409 else none) else (if id = 410 then some localCycle00410 else none)))) else (if id < 414 then (if id < 412 then (if id = 411 then some localCycle00411 else none) else (if id < 413 then (if id = 412 then some localCycle00412 else none) else (if id = 413 then some localCycle00413 else none))) else (if id < 415 then (if id = 414 then some localCycle00414 else none) else (if id < 416 then (if id = 415 then some localCycle00415 else none) else (if id = 416 then some localCycle00416 else none))))))) else (if id < 440 then (if id < 428 then (if id < 422 then (if id < 419 then (if id < 418 then (if id = 417 then some localCycle00417 else none) else (if id = 418 then some localCycle00418 else none)) else (if id < 420 then (if id = 419 then some localCycle00419 else none) else (if id < 421 then (if id = 420 then some localCycle00420 else none) else (if id = 421 then some localCycle00421 else none)))) else (if id < 425 then (if id < 423 then (if id = 422 then some localCycle00422 else none) else (if id < 424 then (if id = 423 then some localCycle00423 else none) else (if id = 424 then some localCycle00424 else none))) else (if id < 426 then (if id = 425 then some localCycle00425 else none) else (if id < 427 then (if id = 426 then some localCycle00426 else none) else (if id = 427 then some localCycle00427 else none))))) else (if id < 434 then (if id < 431 then (if id < 429 then (if id = 428 then some localCycle00428 else none) else (if id < 430 then (if id = 429 then some localCycle00429 else none) else (if id = 430 then some localCycle00430 else none))) else (if id < 432 then (if id = 431 then some localCycle00431 else none) else (if id < 433 then (if id = 432 then some localCycle00432 else none) else (if id = 433 then some localCycle00433 else none)))) else (if id < 437 then (if id < 435 then (if id = 434 then some localCycle00434 else none) else (if id < 436 then (if id = 435 then some localCycle00435 else none) else (if id = 436 then some localCycle00436 else none))) else (if id < 438 then (if id = 437 then some localCycle00437 else none) else (if id < 439 then (if id = 438 then some localCycle00438 else none) else (if id = 439 then some localCycle00439 else none)))))) else (if id < 452 then (if id < 446 then (if id < 443 then (if id < 441 then (if id = 440 then some localCycle00440 else none) else (if id < 442 then (if id = 441 then some localCycle00441 else none) else (if id = 442 then some localCycle00442 else none))) else (if id < 444 then (if id = 443 then some localCycle00443 else none) else (if id < 445 then (if id = 444 then some localCycle00444 else none) else (if id = 445 then some localCycle00445 else none)))) else (if id < 449 then (if id < 447 then (if id = 446 then some localCycle00446 else none) else (if id < 448 then (if id = 447 then some localCycle00447 else none) else (if id = 448 then some localCycle00448 else none))) else (if id < 450 then (if id = 449 then some localCycle00449 else none) else (if id < 451 then (if id = 450 then some localCycle00450 else none) else (if id = 451 then some localCycle00451 else none))))) else (if id < 458 then (if id < 455 then (if id < 453 then (if id = 452 then some localCycle00452 else none) else (if id < 454 then (if id = 453 then some localCycle00453 else none) else (if id = 454 then some localCycle00454 else none))) else (if id < 456 then (if id = 455 then some localCycle00455 else none) else (if id < 457 then (if id = 456 then some localCycle00456 else none) else (if id = 457 then some localCycle00457 else none)))) else (if id < 461 then (if id < 459 then (if id = 458 then some localCycle00458 else none) else (if id < 460 then (if id = 459 then some localCycle00459 else none) else (if id = 460 then some localCycle00460 else none))) else (if id < 462 then (if id = 461 then some localCycle00461 else none) else (if id < 463 then (if id = 462 then some localCycle00462 else none) else (if id = 463 then some localCycle00463 else none)))))))) else (if id < 510 then (if id < 487 then (if id < 475 then (if id < 469 then (if id < 466 then (if id < 465 then (if id = 464 then some localCycle00464 else none) else (if id = 465 then some localCycle00465 else none)) else (if id < 467 then (if id = 466 then some localCycle00466 else none) else (if id < 468 then (if id = 467 then some localCycle00467 else none) else (if id = 468 then some localCycle00468 else none)))) else (if id < 472 then (if id < 470 then (if id = 469 then some localCycle00469 else none) else (if id < 471 then (if id = 470 then some localCycle00470 else none) else (if id = 471 then some localCycle00471 else none))) else (if id < 473 then (if id = 472 then some localCycle00472 else none) else (if id < 474 then (if id = 473 then some localCycle00473 else none) else (if id = 474 then some localCycle00474 else none))))) else (if id < 481 then (if id < 478 then (if id < 476 then (if id = 475 then some localCycle00475 else none) else (if id < 477 then (if id = 476 then some localCycle00476 else none) else (if id = 477 then some localCycle00477 else none))) else (if id < 479 then (if id = 478 then some localCycle00478 else none) else (if id < 480 then (if id = 479 then some localCycle00479 else none) else (if id = 480 then some localCycle00480 else none)))) else (if id < 484 then (if id < 482 then (if id = 481 then some localCycle00481 else none) else (if id < 483 then (if id = 482 then some localCycle00482 else none) else (if id = 483 then some localCycle00483 else none))) else (if id < 485 then (if id = 484 then some localCycle00484 else none) else (if id < 486 then (if id = 485 then some localCycle00485 else none) else (if id = 486 then some localCycle00486 else none)))))) else (if id < 498 then (if id < 492 then (if id < 489 then (if id < 488 then (if id = 487 then some localCycle00487 else none) else (if id = 488 then some localCycle00488 else none)) else (if id < 490 then (if id = 489 then some localCycle00489 else none) else (if id < 491 then (if id = 490 then some localCycle00490 else none) else (if id = 491 then some localCycle00491 else none)))) else (if id < 495 then (if id < 493 then (if id = 492 then some localCycle00492 else none) else (if id < 494 then (if id = 493 then some localCycle00493 else none) else (if id = 494 then some localCycle00494 else none))) else (if id < 496 then (if id = 495 then some localCycle00495 else none) else (if id < 497 then (if id = 496 then some localCycle00496 else none) else (if id = 497 then some localCycle00497 else none))))) else (if id < 504 then (if id < 501 then (if id < 499 then (if id = 498 then some localCycle00498 else none) else (if id < 500 then (if id = 499 then some localCycle00499 else none) else (if id = 500 then some localCycle00500 else none))) else (if id < 502 then (if id = 501 then some localCycle00501 else none) else (if id < 503 then (if id = 502 then some localCycle00502 else none) else (if id = 503 then some localCycle00503 else none)))) else (if id < 507 then (if id < 505 then (if id = 504 then some localCycle00504 else none) else (if id < 506 then (if id = 505 then some localCycle00505 else none) else (if id = 506 then some localCycle00506 else none))) else (if id < 508 then (if id = 507 then some localCycle00507 else none) else (if id < 509 then (if id = 508 then some localCycle00508 else none) else (if id = 509 then some localCycle00509 else none))))))) else (if id < 533 then (if id < 521 then (if id < 515 then (if id < 512 then (if id < 511 then (if id = 510 then some localCycle00510 else none) else (if id = 511 then some localCycle00511 else none)) else (if id < 513 then (if id = 512 then some localCycle00512 else none) else (if id < 514 then (if id = 513 then some localCycle00513 else none) else (if id = 514 then some localCycle00514 else none)))) else (if id < 518 then (if id < 516 then (if id = 515 then some localCycle00515 else none) else (if id < 517 then (if id = 516 then some localCycle00516 else none) else (if id = 517 then some localCycle00517 else none))) else (if id < 519 then (if id = 518 then some localCycle00518 else none) else (if id < 520 then (if id = 519 then some localCycle00519 else none) else (if id = 520 then some localCycle00520 else none))))) else (if id < 527 then (if id < 524 then (if id < 522 then (if id = 521 then some localCycle00521 else none) else (if id < 523 then (if id = 522 then some localCycle00522 else none) else (if id = 523 then some localCycle00523 else none))) else (if id < 525 then (if id = 524 then some localCycle00524 else none) else (if id < 526 then (if id = 525 then some localCycle00525 else none) else (if id = 526 then some localCycle00526 else none)))) else (if id < 530 then (if id < 528 then (if id = 527 then some localCycle00527 else none) else (if id < 529 then (if id = 528 then some localCycle00528 else none) else (if id = 529 then some localCycle00529 else none))) else (if id < 531 then (if id = 530 then some localCycle00530 else none) else (if id < 532 then (if id = 531 then some localCycle00531 else none) else (if id = 532 then some localCycle00532 else none)))))) else (if id < 545 then (if id < 539 then (if id < 536 then (if id < 534 then (if id = 533 then some localCycle00533 else none) else (if id < 535 then (if id = 534 then some localCycle00534 else none) else (if id = 535 then some localCycle00535 else none))) else (if id < 537 then (if id = 536 then some localCycle00536 else none) else (if id < 538 then (if id = 537 then some localCycle00537 else none) else (if id = 538 then some localCycle00538 else none)))) else (if id < 542 then (if id < 540 then (if id = 539 then some localCycle00539 else none) else (if id < 541 then (if id = 540 then some localCycle00540 else none) else (if id = 541 then some localCycle00541 else none))) else (if id < 543 then (if id = 542 then some localCycle00542 else none) else (if id < 544 then (if id = 543 then some localCycle00543 else none) else (if id = 544 then some localCycle00544 else none))))) else (if id < 551 then (if id < 548 then (if id < 546 then (if id = 545 then some localCycle00545 else none) else (if id < 547 then (if id = 546 then some localCycle00546 else none) else (if id = 547 then some localCycle00547 else none))) else (if id < 549 then (if id = 548 then some localCycle00548 else none) else (if id < 550 then (if id = 549 then some localCycle00549 else none) else (if id = 550 then some localCycle00550 else none)))) else (if id < 554 then (if id < 552 then (if id = 551 then some localCycle00551 else none) else (if id < 553 then (if id = 552 then some localCycle00552 else none) else (if id = 553 then some localCycle00553 else none))) else (if id < 555 then (if id = 554 then some localCycle00554 else none) else (if id < 556 then (if id = 555 then some localCycle00555 else none) else (if id = 556 then some localCycle00556 else none))))))))) else (if id < 650 then (if id < 603 then (if id < 580 then (if id < 568 then (if id < 562 then (if id < 559 then (if id < 558 then (if id = 557 then some localCycle00557 else none) else (if id = 558 then some localCycle00558 else none)) else (if id < 560 then (if id = 559 then some localCycle00559 else none) else (if id < 561 then (if id = 560 then some localCycle00560 else none) else (if id = 561 then some localCycle00561 else none)))) else (if id < 565 then (if id < 563 then (if id = 562 then some localCycle00562 else none) else (if id < 564 then (if id = 563 then some localCycle00563 else none) else (if id = 564 then some localCycle00564 else none))) else (if id < 566 then (if id = 565 then some localCycle00565 else none) else (if id < 567 then (if id = 566 then some localCycle00566 else none) else (if id = 567 then some localCycle00567 else none))))) else (if id < 574 then (if id < 571 then (if id < 569 then (if id = 568 then some localCycle00568 else none) else (if id < 570 then (if id = 569 then some localCycle00569 else none) else (if id = 570 then some localCycle00570 else none))) else (if id < 572 then (if id = 571 then some localCycle00571 else none) else (if id < 573 then (if id = 572 then some localCycle00572 else none) else (if id = 573 then some localCycle00573 else none)))) else (if id < 577 then (if id < 575 then (if id = 574 then some localCycle00574 else none) else (if id < 576 then (if id = 575 then some localCycle00575 else none) else (if id = 576 then some localCycle00576 else none))) else (if id < 578 then (if id = 577 then some localCycle00577 else none) else (if id < 579 then (if id = 578 then some localCycle00578 else none) else (if id = 579 then some localCycle00579 else none)))))) else (if id < 591 then (if id < 585 then (if id < 582 then (if id < 581 then (if id = 580 then some localCycle00580 else none) else (if id = 581 then some localCycle00581 else none)) else (if id < 583 then (if id = 582 then some localCycle00582 else none) else (if id < 584 then (if id = 583 then some localCycle00583 else none) else (if id = 584 then some localCycle00584 else none)))) else (if id < 588 then (if id < 586 then (if id = 585 then some localCycle00585 else none) else (if id < 587 then (if id = 586 then some localCycle00586 else none) else (if id = 587 then some localCycle00587 else none))) else (if id < 589 then (if id = 588 then some localCycle00588 else none) else (if id < 590 then (if id = 589 then some localCycle00589 else none) else (if id = 590 then some localCycle00590 else none))))) else (if id < 597 then (if id < 594 then (if id < 592 then (if id = 591 then some localCycle00591 else none) else (if id < 593 then (if id = 592 then some localCycle00592 else none) else (if id = 593 then some localCycle00593 else none))) else (if id < 595 then (if id = 594 then some localCycle00594 else none) else (if id < 596 then (if id = 595 then some localCycle00595 else none) else (if id = 596 then some localCycle00596 else none)))) else (if id < 600 then (if id < 598 then (if id = 597 then some localCycle00597 else none) else (if id < 599 then (if id = 598 then some localCycle00598 else none) else (if id = 599 then some localCycle00599 else none))) else (if id < 601 then (if id = 600 then some localCycle00600 else none) else (if id < 602 then (if id = 601 then some localCycle00601 else none) else (if id = 602 then some localCycle00602 else none))))))) else (if id < 626 then (if id < 614 then (if id < 608 then (if id < 605 then (if id < 604 then (if id = 603 then some localCycle00603 else none) else (if id = 604 then some localCycle00604 else none)) else (if id < 606 then (if id = 605 then some localCycle00605 else none) else (if id < 607 then (if id = 606 then some localCycle00606 else none) else (if id = 607 then some localCycle00607 else none)))) else (if id < 611 then (if id < 609 then (if id = 608 then some localCycle00608 else none) else (if id < 610 then (if id = 609 then some localCycle00609 else none) else (if id = 610 then some localCycle00610 else none))) else (if id < 612 then (if id = 611 then some localCycle00611 else none) else (if id < 613 then (if id = 612 then some localCycle00612 else none) else (if id = 613 then some localCycle00613 else none))))) else (if id < 620 then (if id < 617 then (if id < 615 then (if id = 614 then some localCycle00614 else none) else (if id < 616 then (if id = 615 then some localCycle00615 else none) else (if id = 616 then some localCycle00616 else none))) else (if id < 618 then (if id = 617 then some localCycle00617 else none) else (if id < 619 then (if id = 618 then some localCycle00618 else none) else (if id = 619 then some localCycle00619 else none)))) else (if id < 623 then (if id < 621 then (if id = 620 then some localCycle00620 else none) else (if id < 622 then (if id = 621 then some localCycle00621 else none) else (if id = 622 then some localCycle00622 else none))) else (if id < 624 then (if id = 623 then some localCycle00623 else none) else (if id < 625 then (if id = 624 then some localCycle00624 else none) else (if id = 625 then some localCycle00625 else none)))))) else (if id < 638 then (if id < 632 then (if id < 629 then (if id < 627 then (if id = 626 then some localCycle00626 else none) else (if id < 628 then (if id = 627 then some localCycle00627 else none) else (if id = 628 then some localCycle00628 else none))) else (if id < 630 then (if id = 629 then some localCycle00629 else none) else (if id < 631 then (if id = 630 then some localCycle00630 else none) else (if id = 631 then some localCycle00631 else none)))) else (if id < 635 then (if id < 633 then (if id = 632 then some localCycle00632 else none) else (if id < 634 then (if id = 633 then some localCycle00633 else none) else (if id = 634 then some localCycle00634 else none))) else (if id < 636 then (if id = 635 then some localCycle00635 else none) else (if id < 637 then (if id = 636 then some localCycle00636 else none) else (if id = 637 then some localCycle00637 else none))))) else (if id < 644 then (if id < 641 then (if id < 639 then (if id = 638 then some localCycle00638 else none) else (if id < 640 then (if id = 639 then some localCycle00639 else none) else (if id = 640 then some localCycle00640 else none))) else (if id < 642 then (if id = 641 then some localCycle00641 else none) else (if id < 643 then (if id = 642 then some localCycle00642 else none) else (if id = 643 then some localCycle00643 else none)))) else (if id < 647 then (if id < 645 then (if id = 644 then some localCycle00644 else none) else (if id < 646 then (if id = 645 then some localCycle00645 else none) else (if id = 646 then some localCycle00646 else none))) else (if id < 648 then (if id = 647 then some localCycle00647 else none) else (if id < 649 then (if id = 648 then some localCycle00648 else none) else (if id = 649 then some localCycle00649 else none)))))))) else (if id < 696 then (if id < 673 then (if id < 661 then (if id < 655 then (if id < 652 then (if id < 651 then (if id = 650 then some localCycle00650 else none) else (if id = 651 then some localCycle00651 else none)) else (if id < 653 then (if id = 652 then some localCycle00652 else none) else (if id < 654 then (if id = 653 then some localCycle00653 else none) else (if id = 654 then some localCycle00654 else none)))) else (if id < 658 then (if id < 656 then (if id = 655 then some localCycle00655 else none) else (if id < 657 then (if id = 656 then some localCycle00656 else none) else (if id = 657 then some localCycle00657 else none))) else (if id < 659 then (if id = 658 then some localCycle00658 else none) else (if id < 660 then (if id = 659 then some localCycle00659 else none) else (if id = 660 then some localCycle00660 else none))))) else (if id < 667 then (if id < 664 then (if id < 662 then (if id = 661 then some localCycle00661 else none) else (if id < 663 then (if id = 662 then some localCycle00662 else none) else (if id = 663 then some localCycle00663 else none))) else (if id < 665 then (if id = 664 then some localCycle00664 else none) else (if id < 666 then (if id = 665 then some localCycle00665 else none) else (if id = 666 then some localCycle00666 else none)))) else (if id < 670 then (if id < 668 then (if id = 667 then some localCycle00667 else none) else (if id < 669 then (if id = 668 then some localCycle00668 else none) else (if id = 669 then some localCycle00669 else none))) else (if id < 671 then (if id = 670 then some localCycle00670 else none) else (if id < 672 then (if id = 671 then some localCycle00671 else none) else (if id = 672 then some localCycle00672 else none)))))) else (if id < 684 then (if id < 678 then (if id < 675 then (if id < 674 then (if id = 673 then some localCycle00673 else none) else (if id = 674 then some localCycle00674 else none)) else (if id < 676 then (if id = 675 then some localCycle00675 else none) else (if id < 677 then (if id = 676 then some localCycle00676 else none) else (if id = 677 then some localCycle00677 else none)))) else (if id < 681 then (if id < 679 then (if id = 678 then some localCycle00678 else none) else (if id < 680 then (if id = 679 then some localCycle00679 else none) else (if id = 680 then some localCycle00680 else none))) else (if id < 682 then (if id = 681 then some localCycle00681 else none) else (if id < 683 then (if id = 682 then some localCycle00682 else none) else (if id = 683 then some localCycle00683 else none))))) else (if id < 690 then (if id < 687 then (if id < 685 then (if id = 684 then some localCycle00684 else none) else (if id < 686 then (if id = 685 then some localCycle00685 else none) else (if id = 686 then some localCycle00686 else none))) else (if id < 688 then (if id = 687 then some localCycle00687 else none) else (if id < 689 then (if id = 688 then some localCycle00688 else none) else (if id = 689 then some localCycle00689 else none)))) else (if id < 693 then (if id < 691 then (if id = 690 then some localCycle00690 else none) else (if id < 692 then (if id = 691 then some localCycle00691 else none) else (if id = 692 then some localCycle00692 else none))) else (if id < 694 then (if id = 693 then some localCycle00693 else none) else (if id < 695 then (if id = 694 then some localCycle00694 else none) else (if id = 695 then some localCycle00695 else none))))))) else (if id < 719 then (if id < 707 then (if id < 701 then (if id < 698 then (if id < 697 then (if id = 696 then some localCycle00696 else none) else (if id = 697 then some localCycle00697 else none)) else (if id < 699 then (if id = 698 then some localCycle00698 else none) else (if id < 700 then (if id = 699 then some localCycle00699 else none) else (if id = 700 then some localCycle00700 else none)))) else (if id < 704 then (if id < 702 then (if id = 701 then some localCycle00701 else none) else (if id < 703 then (if id = 702 then some localCycle00702 else none) else (if id = 703 then some localCycle00703 else none))) else (if id < 705 then (if id = 704 then some localCycle00704 else none) else (if id < 706 then (if id = 705 then some localCycle00705 else none) else (if id = 706 then some localCycle00706 else none))))) else (if id < 713 then (if id < 710 then (if id < 708 then (if id = 707 then some localCycle00707 else none) else (if id < 709 then (if id = 708 then some localCycle00708 else none) else (if id = 709 then some localCycle00709 else none))) else (if id < 711 then (if id = 710 then some localCycle00710 else none) else (if id < 712 then (if id = 711 then some localCycle00711 else none) else (if id = 712 then some localCycle00712 else none)))) else (if id < 716 then (if id < 714 then (if id = 713 then some localCycle00713 else none) else (if id < 715 then (if id = 714 then some localCycle00714 else none) else (if id = 715 then some localCycle00715 else none))) else (if id < 717 then (if id = 716 then some localCycle00716 else none) else (if id < 718 then (if id = 717 then some localCycle00717 else none) else (if id = 718 then some localCycle00718 else none)))))) else (if id < 731 then (if id < 725 then (if id < 722 then (if id < 720 then (if id = 719 then some localCycle00719 else none) else (if id < 721 then (if id = 720 then some localCycle00720 else none) else (if id = 721 then some localCycle00721 else none))) else (if id < 723 then (if id = 722 then some localCycle00722 else none) else (if id < 724 then (if id = 723 then some localCycle00723 else none) else (if id = 724 then some localCycle00724 else none)))) else (if id < 728 then (if id < 726 then (if id = 725 then some localCycle00725 else none) else (if id < 727 then (if id = 726 then some localCycle00726 else none) else (if id = 727 then some localCycle00727 else none))) else (if id < 729 then (if id = 728 then some localCycle00728 else none) else (if id < 730 then (if id = 729 then some localCycle00729 else none) else (if id = 730 then some localCycle00730 else none))))) else (if id < 737 then (if id < 734 then (if id < 732 then (if id = 731 then some localCycle00731 else none) else (if id < 733 then (if id = 732 then some localCycle00732 else none) else (if id = 733 then some localCycle00733 else none))) else (if id < 735 then (if id = 734 then some localCycle00734 else none) else (if id < 736 then (if id = 735 then some localCycle00735 else none) else (if id = 736 then some localCycle00736 else none)))) else (if id < 740 then (if id < 738 then (if id = 737 then some localCycle00737 else none) else (if id < 739 then (if id = 738 then some localCycle00738 else none) else (if id = 739 then some localCycle00739 else none))) else (if id < 741 then (if id = 740 then some localCycle00740 else none) else (if id < 742 then (if id = 741 then some localCycle00741 else none) else (if id = 742 then some localCycle00742 else none))))))))))

def namedLeaf000 : LeafData := { rows := ![![5, 4, 3, 2, 1, 6], ![5, 4, 3, 2, 0, 6], ![3, 5, 4, 1, 0, 6], ![2, 5, 4, 1, 0, 6], ![5, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 474 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17792)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![5, 4, 3, 2, 1, 6], ![5, 4, 3, 2, 0, 6], ![5, 3, 4, 1, 0, 6], ![5, 2, 4, 1, 0, 6], ![5, 2, 3, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 275 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17793)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![4, 3, 5, 2, 1, 6], ![4, 3, 5, 2, 0, 6], ![4, 3, 5, 1, 0, 6], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 5, 6], ![2, 1, 0, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 31 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17794)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![4, 3, 5, 2, 1, 6], ![4, 3, 5, 2, 0, 6], ![4, 3, 5, 1, 0, 6], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 6, 5], ![2, 1, 0, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 402 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17795)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![4, 3, 5, 2, 1, 6], ![4, 3, 5, 2, 0, 6], ![4, 3, 5, 1, 0, 6], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![2, 1, 0, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 584 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17796)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![4, 5, 3, 2, 1, 6], ![4, 3, 5, 2, 0, 6], ![4, 3, 5, 1, 0, 6], ![4, 2, 1, 5, 0, 6], ![3, 2, 1, 0, 5, 6], ![2, 1, 3, 0, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 92 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17797)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![4, 5, 3, 2, 1, 6], ![4, 3, 5, 2, 0, 6], ![4, 3, 5, 1, 0, 6], ![4, 2, 1, 5, 0, 6], ![3, 2, 1, 0, 6, 5], ![2, 1, 3, 0, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 697 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17798)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![5, 4, 3, 2, 1, 6], ![4, 3, 5, 2, 0, 6], ![4, 3, 5, 1, 0, 6], ![4, 2, 1, 5, 0, 6], ![3, 2, 1, 5, 0, 6], ![2, 1, 3, 4, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 696 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17799)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![4, 5, 3, 2, 1, 6], ![4, 5, 3, 2, 0, 6], ![4, 3, 5, 1, 0, 6], ![4, 2, 5, 1, 0, 6], ![3, 2, 1, 0, 5, 6], ![2, 3, 1, 0, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 728 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17800)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![4, 5, 3, 2, 1, 6], ![4, 5, 3, 2, 0, 6], ![4, 3, 5, 1, 0, 6], ![4, 2, 5, 1, 0, 6], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 262 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17801)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![5, 4, 3, 2, 1, 6], ![4, 5, 3, 2, 0, 6], ![4, 3, 5, 1, 0, 6], ![4, 2, 5, 1, 0, 6], ![3, 2, 1, 5, 0, 6], ![2, 3, 1, 4, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 728 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17802)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![5, 4, 3, 2, 1, 6], ![5, 4, 3, 2, 0, 6], ![4, 3, 5, 1, 0, 6], ![4, 2, 5, 1, 0, 6], ![3, 2, 5, 1, 0, 6], ![2, 3, 4, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 186 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17803)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![4, 5, 3, 2, 1, 6], ![4, 5, 3, 2, 0, 6], ![4, 5, 3, 1, 0, 6], ![4, 5, 2, 1, 0, 6], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 257 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17804)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![4, 5, 3, 2, 1, 6], ![4, 5, 3, 2, 0, 6], ![4, 5, 3, 1, 0, 6], ![4, 5, 2, 1, 0, 6], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 36 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17805)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![5, 4, 3, 2, 1, 6], ![4, 5, 3, 2, 0, 6], ![4, 5, 3, 1, 0, 6], ![4, 5, 2, 1, 0, 6], ![3, 2, 1, 5, 0, 6], ![3, 2, 1, 4, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 257 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17806)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![5, 4, 3, 2, 1, 6], ![5, 4, 3, 2, 0, 6], ![4, 5, 3, 1, 0, 6], ![4, 5, 2, 1, 0, 6], ![3, 2, 5, 1, 0, 6], ![3, 2, 4, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 400 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17807)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![5, 4, 3, 2, 1, 6], ![5, 4, 3, 2, 0, 6], ![5, 4, 3, 1, 0, 6], ![4, 5, 2, 1, 0, 6], ![3, 5, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 513 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17808)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![5, 4, 3, 2, 1, 6], ![5, 4, 3, 2, 0, 6], ![5, 4, 3, 1, 0, 6], ![5, 4, 2, 1, 0, 6], ![5, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 16 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17809)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 5, 6], ![1, 0, 2, 4, 5, 6], ![1, 0, 2, 3, 5, 6], ![1, 0, 2, 3, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 588 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17810)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 5, 6], ![1, 0, 2, 4, 5, 6], ![1, 0, 2, 3, 6, 5], ![1, 0, 2, 3, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 711 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17811)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 5, 6], ![1, 0, 2, 4, 6, 5], ![1, 0, 2, 3, 6, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 3, 4]], proof := .low6 (![299, 376, 554, 336, 703, 40, 247, 44, 713, 88, 619, 629, 149, 412, 509, 190, 649, 559, 66, 505, 561, 149, 720, 529, 500, 168, 450, 557]) }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17812)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 4, 6, 5], ![1, 0, 2, 3, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 3, 4]], proof := .low6 (![18, 376, 277, 673, 506, 40, 247, 103, 337, 546, 672, 577, 149, 575, 347, 484, 649, 559, 373, 113, 327, 149, 590, 169, 541, 68, 368, 302]) }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17813)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 4, 6, 5], ![1, 0, 2, 3, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 3, 4]], proof := .low6 (![458, 104, 683, 225, 532, 40, 247, 72, 536, 23, 499, 600, 177, 666, 534, 534, 534, 534, 362, 387, 407, 135, 117, 464, 579, 330, 578, 302]) }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17814)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 4, 6, 5], ![1, 0, 2, 3, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low6 (![242, 582, 380, 236, 317, 40, 247, 609, 738, 80, 280, 156, 341, 319, 704, 710, 98, 95, 519, 187, 601, 149, 295, 684, 149, 68, 25, 302]) }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17815)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 5, 6], ![1, 0, 2, 6, 4, 5], ![1, 0, 2, 6, 3, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 4, 3]], proof := .tail 178 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17816)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 6, 4, 5], ![1, 0, 2, 6, 3, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 4, 3]], proof := .tail 112 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17817)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 6, 4, 5], ![1, 0, 2, 6, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 4, 3]], proof := .tail 112 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17818)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 6, 4, 5], ![1, 0, 2, 6, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 4, 3]], proof := .tail 112 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17819)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 4, 5], ![1, 0, 6, 2, 3, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 4, 2, 3]], proof := .low6 (![351, 376, 277, 334, 285, 27, 4, 476, 494, 274, 418, 547, 656, 118, 550, 483, 638, 264, 194, 374, 119, 364, 196, 537, 42, 736, 228, 426]) }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17820)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 4, 5], ![1, 0, 6, 2, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 4, 2, 3]], proof := .low6 (![351, 104, 678, 182, 680, 27, 4, 171, 340, 60, 714, 60, 60, 666, 490, 534, 534, 534, 76, 256, 79, 585, 251, 114, 290, 34, 415, 573]) }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17821)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 4, 5], ![1, 0, 6, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 4, 2, 3]], proof := .low6 (![128, 571, 383, 238, 285, 27, 4, 209, 355, 699, 693, 653, 539, 266, 216, 508, 65, 478, 172, 154, 671, 55, 305, 133, 2, 736, 228, 426]) }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17822)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 4, 5], ![1, 6, 0, 2, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 0, 2, 3]], proof := .low6 (![658, 328, 633, 344, 49, 27, 322, 297, 22, 120, 548, 548, 548, 692, 455, 138, 138, 138, 89, 211, 211, 211, 301, 679, 278, 449, 393, 428]) }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17823)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 4, 5], ![1, 6, 0, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 0, 2, 3]], proof := .low6 (![538, 306, 472, 344, 108, 27, 322, 63, 401, 481, 610, 610, 610, 47, 431, 207, 689, 125, 419, 729, 612, 624, 301, 679, 296, 64, 572, 303]) }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17824)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 0, 2, 3]], proof := .low6 (![367, 361, 130, 719, 664, 27, 4, 105, 357, 219, 611, 622, 210, 339, 439, 436, 343, 26, 259, 381, 69, 74, 307, 650, 81, 566, 434, 426]) }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17825)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 5, 6], ![1, 0, 2, 5, 4, 6], ![1, 0, 2, 5, 3, 6], ![1, 0, 2, 4, 3, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 645 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17826)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 5, 6], ![1, 0, 2, 5, 6, 4], ![1, 0, 2, 5, 6, 3], ![1, 0, 2, 4, 3, 6], ![1, 0, 2, 4, 3, 5]], proof := .low6 (![586, 376, 657, 598, 659, 507, 604, 467, 408, 203, 480, 482, 252, 655, 199, 599, 660, 115, 667, 502, 321, 252, 681, 70, 203, 109, 360, 504]) }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17827)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 5, 6], ![1, 0, 2, 6, 5, 4], ![1, 0, 2, 5, 6, 3], ![1, 0, 2, 4, 6, 3], ![1, 0, 2, 4, 5, 3]], proof := .tail 71 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17828)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 5, 6], ![1, 0, 2, 6, 5, 4], ![1, 0, 2, 6, 5, 3], ![1, 0, 2, 6, 4, 3], ![1, 0, 2, 5, 4, 3]], proof := .tail 102 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17829)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 6, 5, 4], ![1, 0, 2, 6, 5, 3], ![1, 0, 6, 2, 4, 3], ![1, 0, 5, 2, 4, 3]], proof := .low6 (![592, 376, 277, 531, 631, 73, 322, 131, 139, 712, 320, 249, 198, 325, 163, 263, 249, 730, 292, 197, 249, 127, 155, 249, 423, 354, 663, 249]) }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17830)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 6, 5, 4], ![1, 0, 2, 6, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 0, 2, 4, 3]], proof := .low6 (![157, 104, 284, 491, 631, 73, 322, 739, 342, 282, 543, 249, 3, 666, 534, 534, 249, 534, 723, 258, 249, 110, 463, 249, 503, 354, 543, 249]) }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17831)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 6, 5, 4], ![1, 0, 2, 6, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 0, 2, 4, 3]], proof := .low6 (![242, 582, 453, 492, 631, 73, 322, 208, 273, 727, 694, 249, 271, 349, 443, 174, 249, 48, 224, 742, 249, 232, 623, 249, 17, 354, 663, 249]) }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17832)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 5, 4], ![1, 0, 6, 2, 5, 3], ![1, 0, 6, 2, 4, 3], ![1, 0, 5, 4, 2, 3]], proof := .tail 437 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17833)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 5, 4], ![1, 0, 6, 2, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 0, 4, 2, 3]], proof := .tail 644 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17834)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 5, 4], ![1, 0, 6, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 0, 4, 2, 3]], proof := .tail 246 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17835)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 5, 4], ![1, 6, 0, 2, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 4, 0, 2, 3]], proof := .tail 589 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17836)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 5, 4], ![1, 6, 0, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 4, 0, 2, 3]], proof := .tail 589 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17837)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 1, 0, 2, 3]], proof := .tail 241 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17838)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 5, 4, 6], ![1, 0, 2, 5, 4, 6], ![1, 0, 5, 2, 3, 6], ![1, 0, 4, 2, 3, 6], ![1, 0, 2, 3, 4, 5]], proof := .low0 (![41, 627, 359, 148, 377, 618, 145, 395, 569, 636, 50, 50, 20, 641, 395, 395, 395, 395, 404, 469, 469, 20, 97, 435, 435, 32, 20, 20]) }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17839)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 5, 4, 6], ![1, 0, 2, 5, 6, 4], ![1, 0, 5, 2, 6, 3], ![1, 0, 4, 2, 3, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 417 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17840)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 5, 4, 6], ![1, 0, 2, 6, 5, 4], ![1, 0, 5, 2, 6, 3], ![1, 0, 4, 2, 6, 3], ![1, 0, 2, 4, 5, 3]], proof := .tail 520 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17841)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 5, 6, 4], ![1, 0, 5, 6, 2, 3], ![1, 0, 4, 2, 3, 6], ![1, 0, 4, 2, 3, 5]], proof := .low6 (![586, 376, 283, 637, 642, 507, 604, 143, 389, 87, 459, 555, 10, 291, 654, 333, 660, 350, 440, 107, 391, 350, 454, 675, 718, 427, 668, 7]) }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17842)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 6, 5, 4], ![1, 0, 5, 6, 2, 3], ![1, 0, 4, 2, 6, 3], ![1, 0, 4, 2, 5, 3]], proof := .low0 (![701, 627, 420, 148, 593, 618, 145, 395, 731, 229, 501, 501, 20, 511, 395, 395, 395, 20, 479, 94, 94, 21, 97, 435, 617, 32, 630, 403]) }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17843)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 0, 5, 6, 2, 3], ![1, 0, 4, 6, 2, 3], ![1, 0, 4, 5, 2, 3]], proof := .low0 (![512, 627, 432, 148, 460, 618, 145, 395, 686, 59, 86, 96, 20, 269, 395, 395, 395, 20, 218, 390, 390, 411, 97, 435, 700, 32, 630, 403]) }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17844)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 0, 6, 5, 2, 3], ![1, 0, 6, 4, 2, 3], ![1, 0, 5, 4, 2, 3]], proof := .low6 (![662, 376, 277, 304, 518, 27, 4, 524, 643, 366, 564, 57, 175, 276, 639, 549, 737, 206, 194, 121, 121, 121, 202, 346, 366, 378, 669, 13]) }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17845)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 0, 6, 5, 2, 3], ![1, 6, 0, 4, 2, 3], ![1, 5, 0, 4, 2, 3]], proof := .low6 (![662, 104, 406, 238, 315, 27, 4, 323, 695, 709, 239, 220, 488, 666, 534, 534, 534, 534, 385, 39, 517, 134, 698, 111, 709, 298, 615, 386]) }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17846)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 0, 6, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 1, 0, 4, 2, 3]], proof := .low6 (![242, 582, 254, 238, 518, 27, 116, 173, 682, 535, 397, 222, 11, 603, 126, 204, 151, 528, 570, 522, 398, 14, 384, 632, 556, 378, 669, 13]) }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17847)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 6, 0, 5, 2, 3], ![1, 6, 0, 4, 2, 3], ![1, 5, 4, 0, 2, 3]], proof := .tail 235 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17848)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 6, 0, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 1, 4, 0, 2, 3]], proof := .tail 235 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17849)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![6, 1, 0, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 4, 1, 0, 2, 3]], proof := .tail 451 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17850)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 5, 4, 6], ![1, 0, 2, 5, 4, 6], ![1, 5, 0, 2, 3, 6], ![1, 4, 0, 2, 3, 6], ![1, 0, 2, 3, 4, 5]], proof := .low6 (![379, 376, 123, 399, 591, 35, 332, 185, 523, 470, 153, 409, 288, 405, 466, 62, 409, 318, 456, 12, 409, 159, 75, 409, 413, 124, 180, 409]) }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17851)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 5, 4, 6], ![1, 0, 2, 5, 6, 4], ![1, 5, 0, 2, 6, 3], ![1, 4, 0, 2, 3, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 213 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17852)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 5, 4, 6], ![1, 0, 2, 6, 5, 4], ![1, 5, 0, 2, 6, 3], ![1, 4, 0, 2, 6, 3], ![1, 0, 2, 4, 5, 3]], proof := .tail 372 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17853)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 5, 6, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 0, 2, 3, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 493 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17854)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 6, 5, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 0, 2, 6, 3], ![1, 0, 4, 2, 5, 3]], proof := .tail 605 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17855)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 0, 6, 2, 3], ![1, 0, 4, 5, 2, 3]], proof := .tail 205 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17856)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 5, 6, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 0, 2, 3, 6], ![1, 4, 0, 2, 3, 5]], proof := .low6 (![438, 708, 313, 521, 217, 507, 604, 446, 725, 410, 587, 348, 583, 255, 446, 446, 446, 446, 29, 144, 471, 674, 244, 498, 192, 702, 5, 7]) }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17857)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 6, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 0, 2, 6, 3], ![1, 4, 0, 2, 5, 3]], proof := .low0 (![352, 627, 265, 162, 647, 33, 145, 395, 184, 733, 1, 230, 30, 468, 395, 395, 230, 395, 430, 122, 230, 648, 245, 596, 272, 230, 576, 67]) }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17858)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 0, 6, 2, 3], ![1, 4, 0, 5, 2, 3]], proof := .low0 (![635, 627, 311, 425, 647, 33, 145, 395, 165, 78, 1, 230, 685, 195, 395, 395, 230, 395, 430, 122, 230, 77, 152, 212, 272, 230, 576, 67]) }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17859)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 6, 0, 2, 3], ![1, 4, 5, 0, 2, 3]], proof := .tail 356 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17860)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 6, 5, 0, 2, 3], ![1, 6, 4, 0, 2, 3], ![1, 5, 4, 0, 2, 3]], proof := .tail 396 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17861)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 6, 5, 0, 2, 3], ![6, 1, 4, 0, 2, 3], ![5, 1, 4, 0, 2, 3]], proof := .low6 (![242, 137, 472, 462, 294, 27, 116, 527, 706, 24, 640, 442, 422, 129, 279, 514, 562, 300, 38, 100, 634, 61, 191, 99, 179, 448, 9, 533]) }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17862)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 0, 2, 3], ![5, 4, 1, 0, 2, 3]], proof := .tail 243 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17863)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 3, 5, 4, 6], ![1, 0, 2, 5, 4, 6], ![5, 1, 0, 2, 3, 6], ![4, 1, 0, 2, 3, 6], ![1, 0, 2, 3, 4, 5]], proof := .low6 (![54, 376, 602, 399, 591, 35, 604, 185, 523, 470, 153, 409, 661, 670, 487, 200, 409, 163, 665, 732, 409, 661, 75, 409, 413, 124, 180, 409]) }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17864)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 3, 5, 4, 6], ![1, 0, 2, 5, 6, 4], ![5, 1, 0, 2, 6, 3], ![4, 1, 0, 2, 3, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 215 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17865)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 3, 5, 4, 6], ![1, 0, 2, 6, 5, 4], ![5, 1, 0, 2, 6, 3], ![4, 1, 0, 2, 6, 3], ![1, 0, 2, 4, 5, 3]], proof := .tail 91 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17866)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 5, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 0, 2, 3, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 53 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17867)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 6, 5, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 0, 2, 6, 3], ![1, 0, 4, 2, 5, 3]], proof := .tail 84 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17868)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 0, 6, 2, 3], ![1, 0, 4, 5, 2, 3]], proof := .tail 620 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17869)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 5, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 0, 2, 3, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 515 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17870)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 0, 2, 6, 3], ![1, 4, 0, 2, 5, 3]], proof := .tail 382 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17871)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 0, 6, 2, 3], ![1, 4, 0, 5, 2, 3]], proof := .tail 565 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17872)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 0, 2, 3], ![1, 4, 5, 0, 2, 3]], proof := .tail 616 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17873)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 5, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 0, 2, 3, 6], ![4, 1, 0, 2, 3, 5]], proof := .low6 (![248, 329, 526, 545, 363, 507, 604, 46, 142, 45, 324, 331, 691, 82, 416, 132, 625, 267, 457, 597, 250, 10, 146, 6, 10, 427, 525, 7]) }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17874)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 0, 2, 6, 3], ![4, 1, 0, 2, 5, 3]], proof := .low6 (![465, 329, 486, 646, 268, 15, 580, 722, 90, 489, 553, 608, 164, 734, 19, 158, 608, 221, 441, 721, 608, 452, 726, 608, 308, 544, 388, 608]) }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17875)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 0, 6, 2, 3], ![4, 1, 0, 5, 2, 3]], proof := .low6 (![477, 329, 613, 83, 58, 27, 116, 421, 326, 444, 530, 652, 688, 734, 621, 37, 594, 28, 558, 568, 193, 85, 93, 715, 424, 188, 552, 563]) }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17876)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 0, 2, 3], ![4, 1, 5, 0, 2, 3]], proof := .low6 (![314, 281, 286, 375, 43, 27, 116, 497, 0, 429, 183, 495, 688, 234, 496, 740, 226, 166, 445, 293, 516, 140, 201, 261, 433, 447, 705, 581]) }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17877)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 1, 0, 2, 3]], proof := .tail 551 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17878)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 1, 0, 2, 3]], proof := .tail 353 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17879)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 4, 5], ![1, 0, 6, 2, 3, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 4, 3, 2]], proof := .tail 233 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17880)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 5, 4], ![1, 0, 6, 2, 5, 3], ![1, 0, 6, 2, 4, 3], ![1, 0, 5, 4, 3, 2]], proof := .tail 437 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17881)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 0, 5, 6, 2, 3], ![1, 0, 4, 6, 2, 3], ![1, 0, 4, 5, 3, 2]], proof := .tail 724 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17882)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 0, 6, 5, 2, 3], ![1, 0, 6, 4, 2, 3], ![1, 0, 5, 4, 3, 2]], proof := .low0 (![223, 8, 176, 369, 136, 618, 145, 371, 717, 735, 473, 141, 20, 717, 167, 287, 309, 309, 735, 316, 717, 717, 392, 735, 735, 32, 260, 403]) }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17883)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 0, 6, 2, 3], ![1, 0, 4, 5, 3, 2]], proof := .tail 651 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17884)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 0, 6, 2, 3], ![1, 0, 4, 5, 3, 2]], proof := .tail 231 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17885)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 4, 5], ![1, 0, 6, 2, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 4, 3, 2]], proof := .tail 189 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17886)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 5, 4], ![1, 0, 6, 2, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 0, 4, 3, 2]], proof := .tail 147 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17887)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 0, 6, 5, 2, 3], ![1, 6, 0, 4, 2, 3], ![1, 5, 0, 4, 3, 2]], proof := .low0 (![227, 8, 176, 716, 628, 394, 145, 371, 717, 101, 365, 475, 461, 717, 414, 309, 475, 309, 181, 717, 475, 717, 312, 475, 626, 475, 160, 485]) }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17888)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 4, 5], ![1, 0, 6, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 4, 3, 2]], proof := .tail 335 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17889)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 5, 4], ![1, 0, 6, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 0, 4, 3, 2]], proof := .tail 246 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17890)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 0, 6, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 1, 0, 4, 3, 2]], proof := .low0 (![227, 8, 176, 716, 607, 677, 145, 371, 717, 101, 141, 510, 20, 717, 414, 309, 309, 309, 181, 717, 717, 717, 312, 370, 20, 540, 106, 595]) }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17891)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 0, 6, 2, 3], ![1, 4, 0, 5, 3, 2]], proof := .tail 724 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17892)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 0, 6, 2, 3], ![1, 4, 0, 5, 3, 2]], proof := .tail 231 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17893)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 0, 6, 2, 3], ![4, 1, 0, 5, 3, 2]], proof := .tail 724 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17894)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 4, 5], ![1, 6, 0, 2, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 0, 3, 2]], proof := .tail 707 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17895)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 5, 4], ![1, 6, 0, 2, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 4, 0, 3, 2]], proof := .tail 589 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17896)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 6, 0, 5, 2, 3], ![1, 6, 0, 4, 2, 3], ![1, 5, 4, 0, 3, 2]], proof := .tail 235 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17897)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 6, 0, 2, 3], ![1, 4, 5, 0, 3, 2]], proof := .tail 253 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17898)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 6, 5, 0, 2, 3], ![1, 6, 4, 0, 2, 3], ![1, 5, 4, 0, 3, 2]], proof := .tail 396 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17899)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 0, 2, 3], ![1, 4, 5, 0, 3, 2]], proof := .tail 231 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17900)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 4, 5], ![1, 6, 0, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 0, 3, 2]], proof := .tail 676 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17901)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 5, 4], ![1, 6, 0, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 4, 0, 3, 2]], proof := .tail 589 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17902)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 6, 0, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 1, 4, 0, 3, 2]], proof := .tail 235 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17903)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 6, 5, 0, 2, 3], ![6, 1, 4, 0, 2, 3], ![5, 1, 4, 0, 3, 2]], proof := .low0 (![338, 8, 51, 606, 345, 214, 145, 371, 310, 141, 560, 358, 20, 614, 309, 309, 358, 309, 690, 741, 358, 20, 170, 574, 567, 150, 52, 56]) }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17904)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 0, 2, 3], ![4, 1, 5, 0, 3, 2]], proof := .tail 724 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17905)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 0, 3, 2]], proof := .tail 542 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17906)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 1, 0, 3, 2]], proof := .tail 161 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17907)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![6, 1, 0, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 4, 1, 0, 3, 2]], proof := .tail 451 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17908)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 0, 2, 3], ![5, 4, 1, 0, 3, 2]], proof := .tail 243 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17909)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 1, 0, 3, 2]], proof := .tail 724 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17910)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 1, 0, 3, 2]], proof := .tail 237 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17911)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 4, 5], ![1, 6, 0, 2, 4, 5], ![1, 6, 0, 2, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 3, 0, 2]], proof := .tail 687 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17912)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 4, 5], ![1, 6, 0, 2, 5, 4], ![1, 6, 0, 2, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 4, 3, 0, 2]], proof := .tail 589 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17913)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 6, 0, 2, 5, 4], ![1, 6, 0, 5, 2, 3], ![1, 6, 0, 4, 2, 3], ![1, 5, 4, 3, 0, 2]], proof := .tail 235 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17914)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 6, 0, 2, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 6, 0, 2, 3], ![1, 4, 5, 3, 0, 2]], proof := .tail 240 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17915)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 6, 0, 2, 5, 4], ![1, 6, 5, 0, 2, 3], ![1, 6, 4, 0, 2, 3], ![1, 5, 4, 3, 0, 2]], proof := .tail 396 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17916)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 3, 5, 4], ![1, 6, 0, 2, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 0, 2, 3], ![1, 4, 5, 3, 0, 2]], proof := .tail 289 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17917)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 3, 4, 5], ![1, 6, 0, 2, 4, 5], ![1, 6, 0, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 3, 0, 2]], proof := .tail 270 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17918)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 3, 4, 5], ![1, 6, 0, 2, 5, 4], ![1, 6, 0, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 4, 3, 0, 2]], proof := .tail 589 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17919)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (17792 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 17792 ≤ id.val) (hhigh : id.val < 17920) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 17792)) = true := by
  let j : Fin 128 := ⟨id.val - 17792, by omega⟩
  have hsum : 17792 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (17792 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard139
