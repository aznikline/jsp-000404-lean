import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard119
open N4R2RowDataReplay

-- Original cycle 029421dcf0c916931566de1c874b17b3bede21c2bda7e9b2d85c041142f4f8a0; original global index 201.
def localCycle00000 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 2 0, .triangle 4 0, .triangle 23 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 03690d75c7b691ce2cc2a286c82f437f2b53ac8c0febfc4a46e1c6e7d243ab34; original global index 278.
def localCycle00001 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 3 1, .triangle 1 0, .gapLower 3 0]

-- Original cycle 04f8b2ef7aeda52659761a3e3ef3f4f26e6668c67c4b8374589259f90935c0ab; original global index 397.
def localCycle00002 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 1]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 1 3, .gapLower 6 3, .triangle 4 1]

-- Original cycle 05674a94f5eb97a17fa75eb885c618a290bd494e5776e5e08693838ffba28be2; original global index 438.
def localCycle00003 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 34 2, .triangle 23 0, .triangle 2 0, .triangle 1 0, .gapLower 3 0]

-- Original cycle 058b68290964858f3de05942b5712ee7cec1803edc98fbf978264d274430b0f2; original global index 454.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 5 0, .triangle 8 0, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 07e07c900646a2bc8a3d0495af20dff46f0b701dae8bae333cd309f87a74bf48; original global index 636.
def localCycle00005 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 0909167cb5db658f8bc874280367249fc159b8fb51d4e9431b561627da6d22ce; original global index 720.
def localCycle00006 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .triangle 22 0, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 0ea29633a3a2fd0bba1905c215b049014d2ee17610df510cbf4a3481ef5f7ab7; original global index 1156.
def localCycle00007 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 2 6, .distance 2 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 29 1]

-- Original cycle 11559cc59505040b48dd6f51acfe6b02344fdfd15967e6e7c95d1ebbd3338809; original global index 1378.
def localCycle00008 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 25 0, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 11e3b3e33e4e70d26c5d084093c17ea33abec384395440aed1ec381d40b980cc; original global index 1428.
def localCycle00009 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 0 1, .distance 0 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 22 0, .triangle 2 0, .triangle 1 2, .triangle 5 1, .triangle 8 0, .triangle 27 1, .triangle 21 0, .gapLower 3 0]

-- Original cycle 136d09d7a1a53c4278552a248b316a1b21c658e20a85b6f8b2f65107ffd6cce4; original global index 1531.
def localCycle00010 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 4, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 1bfbce5fd265b28e054f6275fdc31bdbcb4cd667fff19d987633f8d31f62c064; original global index 2161.
def localCycle00011 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 0, .gapLower 4 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 1c01f686240777880ec7c3d76db8ac11fabf1c4dd8620af98330c5594a23bf2c; original global index 2164.
def localCycle00012 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 3]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 2, .gapLower 6 4, .gapLower 6 3, .triangle 11 1]

-- Original cycle 1ccc02898d4940af4d29b1fdbcc283702cf53e189a5a6c7bcd8d7ce1ab48c83c; original global index 2213.
def localCycle00013 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 23 0, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 1f7236093657e4eb1a32d7351f2078aba7e8017b8a4b588e587dcab35cdeb877; original global index 2416.
def localCycle00014 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 12 0, .triangle 2 1, .triangle 1 0, .gapLower 3 0]

-- Original cycle 1fcab75c46fd062d53eb4753d82f504a8dc6c5fcec1ebb4acf4e0f05d9c49f5d; original global index 2441.
def localCycle00015 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 1fdd41cf76c7c0afb6ec337526df61c411985133905980b2b15f91c6dddc076e; original global index 2447.
def localCycle00016 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 32 1, .gapLower 4 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 213052efe8c5261671752210076bf353c64089e5155ec06288daf1ef706d6db0; original global index 2544.
def localCycle00017 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 19 2, .triangle 23 0, .triangle 13 0, .triangle 2 1, .triangle 1 0, .gapLower 3 0]

-- Original cycle 217a0f61d52c3f896343f31e37cb1da1a7013a700049c8156dd517450dbf7de7; original global index 2563.
def localCycle00018 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 219807b7577bafab85ba4a72141b0b69ed44f7b7c6e2e07243b36435245817c4; original global index 2571.
def localCycle00019 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![0, 2, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 7 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 5 0]

-- Original cycle 22a1f2322aba486f358da8bef4de40634c4599014fab070abfbd6d2cec43cc3e; original global index 2653.
def localCycle00020 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 5 0, .triangle 7 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 24c9446cf269a5fd94792d27a227ac046f64a1fc0f888713f24890561d67e6dd; original global index 2821.
def localCycle00021 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![0, 0, 2, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 5 1, .gapUpper 2 2, .gapLower 5 4, .triangle 31 0, .triangle 19 2, .triangle 2 0]

-- Original cycle 2635297b00d86aeefaf6d1303b91c70efdde0a3f0ca8e1d8243fa4d12fb0006a; original global index 2930.
def localCycle00022 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 3 6, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .gapLower 6 4, .triangle 21 2, .triangle 23 1, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 2bbddc23486d6af38f73c8842acb31c74cfd02101eaef934b38d210422b23924; original global index 3342.
def localCycle00023 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 2, .gapLower 6 2, .triangle 13 1, .triangle 2 1, .triangle 1 0, .gapLower 3 0]

-- Original cycle 2fed245fa739ad41c2f04ceeaea9f6dacfafd488b5267461c62c1d2105f6d18b; original global index 3657.
def localCycle00024 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 3 6, .distance 0 3, .distance 0 2]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .triangle 11 0, .triangle 5 1]

-- Original cycle 3062dc1602093a48349181edefa40afbdfe74fa7a59099f98347b28b26b434df; original global index 3683.
def localCycle00025 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 2 1, .triangle 1 0, .gapLower 3 0]

-- Original cycle 310e1e59934231519148b4069557484502711c5e4966f4474fc211bf5248ea2c; original global index 3737.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 1, .gapLower 6 3, .triangle 4 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle 31358b8025dee637b8fafb0bbdb9efdd6ff9669268c16b2e2e21f735d88c5fba; original global index 3754.
def localCycle00027 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 28 0, .triangle 16 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 31cee540a5ce8ec636608dfff4bb9760b8260317e4e7b2351d964d6a50469e7b; original global index 3805.
def localCycle00028 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .triangle 22 1, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 32089bac075f455826a255f63c2a93ab6a85e39cc4384dbcc82ae90dcf6a39db; original global index 3820.
def localCycle00029 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .gapLower 6 2, .triangle 4 1, .triangle 1 0, .gapLower 3 0]

-- Original cycle 340fadfdbe357b410b8fdb977952ccb8cc0097424f18ed0616f8a058f06123f9; original global index 3990.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 21 2, .gapLower 6 2, .triangle 4 1, .triangle 1 0, .gapLower 3 0]

-- Original cycle 346635b338b809dc82f7fa8b22310a5ef23b3381f79e16c21df159df71c60569; original global index 4015.
def localCycle00031 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 0, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 375871330bbab51c7bda71fb133729a31c2d0e681ae6ed776682283ae717298f; original global index 4252.
def localCycle00032 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 34 0, .triangle 14 0, .triangle 3 1, .triangle 1 0, .gapLower 3 0]

-- Original cycle 38524091a57750c6365f2cc9d563cc0f6664e58055b485b769aa1ad5d33d9c62; original global index 4326.
def localCycle00033 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 13 0, .triangle 2 1, .triangle 1 0, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 39d74a5e220bd7b8a82907f6d9f220b543201c10f2b639591a1e3673e153573a; original global index 4463.
def localCycle00034 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 3a0e5824b1f674fc6a3ebb6d8edb449c4e6527e5ef08378ad81fd28865df7cce; original global index 4479.
def localCycle00035 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 21 2, .triangle 4 0, .triangle 1 0, .triangle 15 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 3b3e644e1a8c0ee712cc17308adb42f3fd1ef319da92a0d5aa59e4c97fe9c484; original global index 4576.
def localCycle00036 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 3 6, .distance 0 3, .distance 0 2]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .triangle 11 0, .triangle 5 1]

-- Original cycle 3c152c44b3b8698f4001cfa5266668fbba69886baa450836e55cf80f79c67a7a; original global index 4657.
def localCycle00037 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 0 1]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 1 2, .gapUpper 3 2, .gapLower 6 4, .triangle 4 0]

-- Original cycle 3cb2d599145ab117e2effd3f2e436423fbf685987161027cb2f50b8eac6e75da; original global index 4708.
def localCycle00038 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .gapLower 4 3, .triangle 22 0, .triangle 12 0, .triangle 2 1, .triangle 1 0, .gapLower 3 0]

-- Original cycle 3d0611dce37c6a87abe1d39b6bffe4a722580ec4f429c6ed2c2b84e6bc04db85; original global index 4725.
def localCycle00039 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 3fb463a6401679eed106d2c5e8465f38b05aa461c600fc57af57422db72e04e5; original global index 4918.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 13 0, .triangle 2 1, .triangle 1 0, .gapLower 3 0]

-- Original cycle 4384f5e809a6cc6a5e66cb04936dffc23dfb4ea581f3f3d8037f91c75de01573; original global index 5217.
def localCycle00041 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 14 0, .triangle 3 1, .triangle 1 0, .gapLower 3 0]

-- Original cycle 44abea3d61130b54e0edf8d8a17e70447e82ba2ad312968e285af09ea2260bb0; original global index 5319.
def localCycle00042 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .triangle 4 0, .triangle 1 0, .gapLower 3 0]

-- Original cycle 452a47ad1eaed52a29541673c9edd208a3a137a7ea83002d4d835e7f1df390ac; original global index 5350.
def localCycle00043 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 48924468c9fae83c5a4a6da92e280d75745c0dc9aba97597b025d193b674144d; original global index 5621.
def localCycle00044 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 3, .distance 1 2, .theta 2]
    constant := ![4, -1, 0, -3, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 2 6, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .triangle 4 0, .triangle 1 0, .triangle 15 1, .gapLower 2 0]

-- Original cycle 4a7d14a0c8f47c284c90d036129ac35c8c3a0295a347aa9e790fae98ba591dca; original global index 5777.
def localCycle00045 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 19 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 4afccdafaa307676738cd958483e525c92249500f75b8254e7296bc7c877f0b0; original global index 5820.
def localCycle00046 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .gapLower 4 3, .triangle 2 0, .triangle 4 0, .triangle 23 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 4ba4b7b27dd85d0ddfaab76dd99ae3e468e286d5b0554d37486e56a9c104f487; original global index 5871.
def localCycle00047 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 32 2, .gapLower 6 4, .triangle 4 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 4e2ab306ca8acd803e2f1b0637085d71e6c1cd33629f2059e22d2fe731445e4a; original global index 6067.
def localCycle00048 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 9 0, .triangle 11 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 4e314d1e74bf636ad05e1619f45aa45f9dc0009a511069b7726407fc8e0745a9; original global index 6068.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 0, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 4f7466eb9cd6b18ba0ffa0021a767ce1cc831aa1a3b5ec70d658140c8c1f894d; original global index 6174.
def localCycle00050 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 5 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 4f7fa1f73319ab86b2aa9e1b4bb987e0fd2f39e0bc547000d6491ad992f16ba3; original global index 6176.
def localCycle00051 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 5, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 5 0, .triangle 7 0, .triangle 17 2, .triangle 20 1, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 4f88e56c34da8da33e62ec6a7d422529feea05607619518651e125207532de7e; original global index 6178.
def localCycle00052 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 0, .triangle 2 0, .triangle 1 0, .triangle 15 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 4fb6edf5c20d2771e5c0fe364d38c83cce9d0976bdae39be84d58a6110455a75; original global index 6190.
def localCycle00053 : Cycle where
  length := 3
  data := {
    node := ![.theta 5, .distance 5 6, .theta 6, .theta 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 0, .gapLower 6 0, .thetaNext 5]

-- Original cycle 50839df3e2f48563a0e47ca155f480c8b5da4a1fc753d9d5f91970011e9d4357; original global index 6251.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 13 0, .triangle 2 1, .triangle 1 0, .gapLower 3 0]

-- Original cycle 5502b8a4cf3a43371eb0d02549343751d7f4add2333067abf708c76706e19137; original global index 6582.
def localCycle00055 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 582e2c14daff953d680b9d2a842de3e9b04f5490cfdb855c6294872cfaf36eb8; original global index 6841.
def localCycle00056 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![4, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 26 1, .triangle 25 0, .triangle 19 2, .triangle 2 0, .triangle 1 0, .gapLower 3 0]

-- Original cycle 5d221105158e0341185d6078417ac3a2e6d375e71831a0dbe9d7c8698d862d00; original global index 7248.
def localCycle00057 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 28 0, .triangle 29 2, .gapLower 6 5, .triangle 11 2, .triangle 13 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 5df4c8c6abb3a5042461d452a2fdbbe5798664111de428039fd94329ce710571; original global index 7308.
def localCycle00058 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 11 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5f2739f5ff70c11150b1c2b3a82b18bc28e797e5eb50c69d8e24a645b27eea1c; original global index 7409.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 12 0, .triangle 2 1, .triangle 1 0, .gapLower 3 0]

-- Original cycle 5fa52e2ac67c6ffd5102d463f143cc03df1a12f50c3ad4d54d7b3474337294f6; original global index 7451.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .triangle 2 0, .triangle 1 0, .gapLower 3 0]

-- Original cycle 60af1751d6b74ce24cd9173f2e0bd63c07178a5f12a3b391a043b9dcdcc7e93a; original global index 7529.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 2, .gapLower 6 2, .triangle 4 1, .triangle 1 0, .gapLower 3 0]

-- Original cycle 60d1efe918b823f2ca19def0b78b8c23cdfa1e6784974ff93d4f50345bce9282; original global index 7541.
def localCycle00062 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 1 2, .triangle 11 0, .triangle 21 0, .triangle 15 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 64015fd4965d37d2ef941cc004a1e5b8dc49d947b3f85242c94fd575ad739ae9; original global index 7793.
def localCycle00063 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 2 1, .triangle 1 0, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 648e5ba6aeffa539abf11397fac2b48dcc5ed7dc9c71f393944920fa84e86717; original global index 7836.
def localCycle00064 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 1 2]
    constant := ![-1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 17 0, .triangle 30 0, .triangle 33 2, .gapUpper 3 2, .triangle 15 1]

-- Original cycle 65465ed4122738a2045babc166b0a169ee077640ffa4715c575445ed0bac5e3e; original global index 7880.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 31 0, .triangle 22 0, .triangle 2 0, .triangle 1 0, .gapLower 3 0]

-- Original cycle 67129153b101b55ba25fba2b792f8523e6db2cef469b8315e3196de3313d227a; original global index 8009.
def localCycle00066 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 0, .gapLower 4 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 6909c8910dfb982b7a90776755e9bcd64ed1f863703684d2a98519536d20657b; original global index 8170.
def localCycle00067 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .gapLower 4 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 6bc2cdf35ba002882bf3ec722351ba77036de1f369697028711e1fbc1a3f51f0; original global index 8390.
def localCycle00068 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 22 0, .triangle 2 0, .triangle 1 0, .gapLower 3 0]

-- Original cycle 6f49f7a84deba72d6b3ba2244c191d4a1c061fb7b252cfd5268781885eb6fb99; original global index 8624.
def localCycle00069 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 8 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 704b6cb1e1f33dd77077d3262281d27d77aaec123524e52662eb5d0b538f7aca; original global index 8700.
def localCycle00070 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 721aa15246990bc1d37b6969e36b687f1b31ce98e32db0a1ae541d33258fc98f; original global index 8845.
def localCycle00071 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 12 0, .triangle 2 1, .triangle 1 0, .triangle 21 0, .corridorLower 3 6]

-- Original cycle 73053451d48d85af58eaea2d1e04821c771743e9deb63794c5ceaf1ab144cb42; original global index 8911.
def localCycle00072 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 22 0, .triangle 2 0, .triangle 4 0, .triangle 23 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 786f3d477577e1d75839f6020ac7f5f768e59aecb121ce3178fc2f19dc6bb113; original global index 9315.
def localCycle00073 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 5 6, .triangle 12 0, .triangle 13 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 7a2aa2b0465d2c78c5134e15507d018f890075a6dfd35368dca2e1d604c905da; original global index 9448.
def localCycle00074 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 3 6, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 11 0, .triangle 21 0, .gapLower 3 0]

-- Original cycle 7a91906fbb4109bfa2065f9396ad384dc456ea94b426afb0eafa8f1c4a02a5cc; original global index 9483.
def localCycle00075 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 22 0, .triangle 2 0, .triangle 1 0, .triangle 15 1, .triangle 18 0, .triangle 27 1, .corridorLower 3 6]

-- Original cycle 7b7faf316ac15257e0bc1520a192b509eb09e463307e743db4003400c6901d4f; original global index 9557.
def localCycle00076 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 7cc5b77f7a37f9df1e0c248c48adda039326a8fc96cd6876375bd33cd98fb286; original global index 9665.
def localCycle00077 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 7d91bada1cffa8734f2d50ae68ea10748af36bc57e9af21856ed776f1629f532; original global index 9746.
def localCycle00078 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 3 6, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 21 2, .triangle 23 1, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 831363a8de34c2583abaa2fe0010bbd4e1bf70a6e41522e82948c705020e8b57; original global index 10165.
def localCycle00079 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 3, .triangle 13 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 842d8fac132ca5649501535ef1added63865252dde6572bd41b15ca37514921d; original global index 10262.
def localCycle00080 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 2, .triangle 24 0, .triangle 14 0, .triangle 12 1, .triangle 2 1, .triangle 1 0, .gapLower 3 0]

-- Original cycle 8934479d35c2f57bb503b99c8b356f20475040c430e27bd43f79899f5da9b7cf; original global index 10617.
def localCycle00081 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 5, .triangle 11 2, .triangle 13 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 89f497c74eb812d328b5baa6d4003a4e0873bab24a1d40b554c4dacd9513455b; original global index 10692.
def localCycle00082 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 32 2, .triangle 21 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 8ae4eaa36f7d9f10b04449a50263b5de1b1064e0514ff1800bd8b89ff7740a60; original global index 10761.
def localCycle00083 : Cycle where
  length := 14
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .gapLower 4 3, .triangle 2 0, .triangle 1 0, .triangle 15 1, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 8cc92a4d8171069c971ba95c7eb68594d62c46b0a530d0a3c5592c99ff132aaa; original global index 10888.
def localCycle00084 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 34 2, .triangle 13 0, .triangle 2 1, .triangle 1 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 8dcc10854dd98d1215a9e662ff3b9ffc69ec89a246deb868ae1536b0dcb79a75; original global index 10973.
def localCycle00085 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 8dcf6899888c0111b8be2e3ea4b25129955fd93935779fa12fac181b27bb595f; original global index 10975.
def localCycle00086 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 2, .gapLower 6 2, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 8ef3c87aa5d233220affdf8bacb5fe8b3e16e2ba67d0aa890400ab257df59299; original global index 11058.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .gapLower 4 3, .triangle 22 0, .triangle 12 0, .triangle 2 1, .triangle 1 0, .gapLower 3 0]

-- Original cycle 8efd54dfc5fd73abd6ae98880c5379799fd846255d3ec00d23e58fa3c33960b2; original global index 11061.
def localCycle00088 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 2 0, .triangle 1 0, .triangle 15 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 8f10652ba17d5c4d172fc824e62815d614b3192f972970c87910424c71008a9d; original global index 11070.
def localCycle00089 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 4, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, 0, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .gapLower 4 3, .triangle 23 2, .gapLower 6 3, .triangle 4 1, .triangle 1 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 9054b3354095aafd64a78cfa129de079aa71e9caf672c060765d6abfeb40385b; original global index 11175.
def localCycle00090 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 9 0, .triangle 11 0, .triangle 21 0, .gapLower 3 0]

-- Original cycle 91dd99453af960e8e88ac6aa83160ea4b187b360bba725ef7fddda773f20ce8f; original global index 11304.
def localCycle00091 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 3 6, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, 0, 0, -3, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 21 2, .triangle 23 1, .triangle 2 0, .triangle 1 0, .gapLower 3 0]

-- Original cycle 928713b3dc836dc5dd293e65cb7b13534b205c8de6bfdfb63fe0eee618161b61; original global index 11350.
def localCycle00092 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 13 2, .gapLower 6 2, .gapUpper 4 1]

-- Original cycle 9961fc01595299ba0fd9b695628a9a01219dd4905cd1225caecf7be6972e9dbc; original global index 11910.
def localCycle00093 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 23 0, .triangle 2 0, .triangle 1 0, .gapLower 3 0]

-- Original cycle 9a6136efb2892e530f5bd1eaf0c4949ff63c8bf8905a9af6450cfcc6b4d0c50c; original global index 11997.
def localCycle00094 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 2]
    constant := ![2, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .gapLower 6 4, .triangle 4 2, .triangle 8 1]

-- Original cycle 9a85702d176a7aeed11e6a22f4e67792995627072d4101e08752a5ddc6505b08; original global index 12004.
def localCycle00095 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 9b5172cc4dbf2f3ec203690bd2e6db162762a964492687dba397125a11c8f836; original global index 12079.
def localCycle00096 : Cycle where
  length := 13
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .gapLower 4 3, .triangle 2 0, .triangle 1 0, .triangle 15 1, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 9dc98bcbff2e5ab92dbb8f185a67ae81e0cf570a24bd3a26105901d18a8dac32; original global index 12274.
def localCycle00097 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .gapLower 4 3, .triangle 2 0, .triangle 1 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 9dde1d1babb84daa5405e78d5ed6bf8d4aa852146efebd91d8618874077bf3b7; original global index 12284.
def localCycle00098 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 31 0, .gapLower 4 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle a236a14d65355e7004dc0736b9ee05ec49e75d0c657a306eb8d3ba2bb23857be; original global index 12621.
def localCycle00099 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 34 0, .triangle 24 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle a73a4a4cced292de90f78cbc165ef733ddfaa786481c467bbce2113ce3b73d19; original global index 13003.
def localCycle00100 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 19 2, .triangle 2 2, .triangle 13 0, .triangle 34 1, .corridorLower 5 6]

-- Original cycle a771d11cce0c0ad26eab2e9ed905801dd1651b89c4c4c7ed9f07d7de6a45a729; original global index 13026.
def localCycle00101 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 5 0, .triangle 7 2, .triangle 14 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle a9c3933ce1e1b4ae7703dc6bfba95dc75baf81470090993131a483c445287335; original global index 13218.
def localCycle00102 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 11 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle afb5a9ae46c11f538da6e4ea93680ed060b32505335b778fa472aff1cc517bb4; original global index 13724.
def localCycle00103 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 3]
    constant := ![2, -3, 0, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.gapUpper 3 2, .gapLower 6 4, .triangle 4 2, .triangle 11 1]

-- Original cycle b2746043fd05eb6e1e254ca57be55afa3085136bbbfcb6535abfb57f97767812; original global index 13943.
def localCycle00104 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 0, .triangle 25 0, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle b627dda634245f6695376b5b04b7503bbf3afd7f46355bb7463ce63c5c8878ee; original global index 14226.
def localCycle00105 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 32 2, .triangle 11 2, .gapLower 6 2, .corridorLower 4 6, .thetaNext 3]

-- Original cycle b877eeebda969328cae19ff1c93c4ca4455034f462158f9951a90faa17899ad8; original global index 14394.
def localCycle00106 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 19 2, .triangle 22 0, .triangle 12 0, .triangle 2 1, .triangle 1 0, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle b8dc282fd4be383a7ffa7237ffa3a392de35c141eb629356fa1c4362dc083f12; original global index 14430.
def localCycle00107 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .gapLower 1 4, .triangle 2 0, .triangle 1 0, .gapLower 3 0]

-- Original cycle ba18698425ab07121ffed9d5b6da6f791116945876cdc7d177690c02483c497e; original global index 14532.
def localCycle00108 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .gapLower 5 3, .triangle 3 0, .triangle 1 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c1ea8f393f0d4d3ca7435a271d0303964fae25cbb85c34a6590862f6a2232ce7; original global index 15140.
def localCycle00109 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 11 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle c1ec03dc8489ad626b60ea9bfbd5a1406f86aa5a57b7fe103789aef3b7ce51c8; original global index 15141.
def localCycle00110 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 0, .triangle 21 1, .triangle 15 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle c57535aaac11eeee43290649732e08aef746cd681642c2bf5ed3cf1f95e82958; original global index 15406.
def localCycle00111 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .theta 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -2, 2, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .gapLower 6 0, .gapLower 6 6, .triangle 23 0, .triangle 2 0, .triangle 1 0, .gapLower 3 0]

-- Original cycle c5ee6ab3c99ace5c24820f0ce2b450ffb583fae3b9682630f56338ab18b74576; original global index 15435.
def localCycle00112 : Cycle where
  length := 13
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .gapLower 4 3, .triangle 2 0, .triangle 1 0, .triangle 15 1, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle c781294450e83b072d240a77a9d433680bcf3a881cee33ca1416404627715815; original global index 15570.
def localCycle00113 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 14 2, .gapLower 6 1, .gapUpper 5 1]

-- Original cycle c7a4fe279e1d82604c941afdc8cbdc2cb0a1990ba848a71aefd13c9a211fcee9; original global index 15581.
def localCycle00114 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 22 0, .triangle 2 0, .triangle 1 0, .triangle 21 0, .corridorLower 3 6]

-- Original cycle c85724968b70937f781a1b2bf1066aa662cb8eab6eea9c5a8a194e03c53d87b2; original global index 15638.
def localCycle00115 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![2, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false, true] }
  origin := ![.gapUpper 2 2, .triangle 30 1, .triangle 34 2, .triangle 32 0, .gapLower 4 3, .triangle 22 0, .triangle 12 0, .triangle 6 1]

-- Original cycle caba392f9d03fc96de26223cd8192cad09ac33d4b1a676928897f3137c01efd2; original global index 15848.
def localCycle00116 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 18 2, .triangle 4 0, .triangle 1 0, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle cb232157a14d560105a101fbf3be9117d0788373fbcdd98c2ab83bac41f16cbf; original global index 15868.
def localCycle00117 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 22 0, .triangle 2 0, .triangle 1 0, .gapLower 3 0]

-- Original cycle cc507c1ea0c0235e01e0ed9c8625ade4beecac3bd41acda74fc3f7f811d8dd98; original global index 15968.
def localCycle00118 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, false, false, true, true, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle cc64a0f0918b65dea053d9a992be2f779d12c632fb9d8da28d1c79742f2f9dc6; original global index 15973.
def localCycle00119 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -2, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 18 2, .triangle 23 1, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle cd04e24d998851a216bd33c2b95a2ec69c98383bbba7ad50863d04ae43f01d9d; original global index 16021.
def localCycle00120 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .gapLower 4 3, .triangle 2 0, .triangle 1 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle d0bfc31fc338e7318f5c8e74c7b147bc620b35687394073597400e35157ffb3c; original global index 16293.
def localCycle00121 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 4, .triangle 2 0, .triangle 1 0, .gapLower 3 0]

-- Original cycle d42ee582f0ceb7f3b40704285ffba2b91eac0b7b131c7b2fcc1e9eac0e607d74; original global index 16559.
def localCycle00122 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .gapLower 4 3, .triangle 2 0, .triangle 4 0, .triangle 23 1, .corridorLower 4 6]

-- Original cycle d7508d4698c86a1c782d6b795770eb06bc821d4757289cab04bce58f969217db; original global index 16803.
def localCycle00123 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 22 0, .triangle 23 2, .gapLower 6 3, .triangle 13 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle d9f650c2904e3f40efa7305dc0122152abcdd230d2a49cd08d424ae5c374d112; original global index 17031.
def localCycle00124 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 31 0, .triangle 22 0, .triangle 2 0, .triangle 1 0, .gapLower 3 0]

-- Original cycle da7297a3056773fccac1039e6fc8e144fcfacfee25768cfe735af703b77de4ac; original global index 17072.
def localCycle00125 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 0, .triangle 18 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle daaf46593b48b78a8eb3f9a4a5fa49cd7e803fdb1d74a65343cf02a1f4027f76; original global index 17089.
def localCycle00126 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 0, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle dc3629dc42c9892a1d866749d05ac408d09d0eb000483aabca417cd7bad36dd6; original global index 17210.
def localCycle00127 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 2, .gapLower 6 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle dda7cc972e249f19e284b3d6249e6d2f48a454e3e5e69b0261b65a23eeec47ff; original global index 17325.
def localCycle00128 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle ddde7f9c236a7871a0a16f65d58ad69f2adbd6bbaf616e9d1c29763b4c2ac33c; original global index 17344.
def localCycle00129 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 2]
    constant := ![2, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .triangle 21 2, .gapLower 6 3, .triangle 8 1]

-- Original cycle de169ad8a82f2ac15c936e7b752f812e5a6e72f50975f29f1443fbe932dd6e38; original global index 17368.
def localCycle00130 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .gapLower 4 3, .triangle 2 0, .triangle 1 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle de941b4df4f1044fd76d9247edb4588ad3605b89f3a646dc203a81bca1a42220; original global index 17403.
def localCycle00131 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 22 0, .triangle 2 0, .triangle 1 2, .triangle 11 0, .triangle 21 0, .gapLower 3 0]

-- Original cycle debe7a2d1ca06c895c3330cc05afcecbc604b647d339dcb1e086f89a4c3dad86; original global index 17415.
def localCycle00132 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 3, .gapLower 4 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle e044ef0022aea950e0216e6f04aee0f6837c6255f593cccb20da42f45f1007f6; original global index 17533.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 23 0, .triangle 22 0, .triangle 12 0, .triangle 2 1, .triangle 1 0, .gapLower 3 0]

-- Original cycle e243376164bf16ba24ebe99fe4cb6dd3761c44b017a03821056cad3c5322336e; original global index 17688.
def localCycle00134 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 32 0, .triangle 23 0, .triangle 2 0, .triangle 1 0, .gapLower 3 0]

-- Original cycle e28265b97e617a826e0f3d4450743b7c6bc77a345590e052478dc06a6e18c823; original global index 17712.
def localCycle00135 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 18 2, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle e45badc73fc07d64c1c1f79426c8908308b0b7eb94055bd4327d95d2588bb1e7; original global index 17851.
def localCycle00136 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 2 1, .triangle 1 0, .triangle 15 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle e4f994e8ff6e1d7cc12b538e16c9a02d7f5e5aaace629cab749391da079e6184; original global index 17902.
def localCycle00137 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle e5d19427f319b6445053f28580f92ed882f90fe317b96e1095a5a39280eef4d6; original global index 17981.
def localCycle00138 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 4 5, .distance 2 4, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![4, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 28 0, .triangle 29 2, .gapLower 6 5, .triangle 11 2, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle e7de3346147594921ae7ff248173ba5f8d4abb1c23af0a1c5d1b54c323accc03; original global index 18133.
def localCycle00139 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 0, .triangle 32 2, .gapLower 6 4, .triangle 4 2, .triangle 13 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle ebaea39b53b3f8a2861f2aa3c0ae3bb9b953f7a45b76648c7e9155fb4c4612f1; original global index 18392.
def localCycle00140 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 12 0, .triangle 13 0, .corridorLower 4 6, .thetaNext 3]

-- Original cycle ebe7a94865f52ac4a84de3c438f2f72f45c38b2c2331a94df30686cfc2f2c15a; original global index 18412.
def localCycle00141 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .triangle 17 0, .triangle 26 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle edb93069209de7b9f44d773481f80ac6e3cbd64281c4f943e59fa3b97c47b22f; original global index 18559.
def localCycle00142 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 4, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle ee55424d1a3cca626e6947ac5c9b27dc936cc59f89a4ca1b2eff62e751a90bcb; original global index 18603.
def localCycle00143 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 0, .triangle 1 0, .triangle 15 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle f1cec315ddafba3db83c7b7f1f7d8204603656b2e4f4743b9c8c205c0cac4307; original global index 18855.
def localCycle00144 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .triangle 2 0, .triangle 1 0, .gapLower 3 0]

-- Original cycle f226acc00c2973711755d7f51b41d722385e85fee89d6b129d8d9f36777f0e9c; original global index 18884.
def localCycle00145 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 0, .gapLower 3 3, .triangle 11 0, .triangle 21 0, .gapLower 3 0]

-- Original cycle f982cd6690cec02be80288e65351f074e4a193c8e04fccbb6a324cca1615bd37; original global index 19453.
def localCycle00146 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .gapLower 1 4, .triangle 2 0, .triangle 1 0, .gapLower 3 0]

-- Original cycle f9c46ffd05d7c141cfda43721f71ddf3358938d50fe7456d2410fe31fe040328; original global index 19477.
def localCycle00147 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 4, .triangle 2 0, .triangle 1 0, .gapLower 3 0]

-- Original cycle fbaf2ee2975afa002b43547b09f7a7e2422b802d1de2f4826ce8410fae786fe2; original global index 19649.
def localCycle00148 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 13 0, .triangle 2 1, .triangle 1 0, .triangle 15 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle fbbd10b6ff3d58fc278a4bbfc400b18764a9ca8f871da3722e0f9f79eab53be8; original global index 19650.
def localCycle00149 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 12 0, .triangle 2 1, .triangle 1 0, .gapLower 3 0]

-- Original cycle fd802b4f9337ee245968526b504db4c1164afa54f2b79d24626adea5adbed93b; original global index 19813.
def localCycle00150 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 3, .theta 3]
    constant := ![3, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .triangle 1 0, .gapLower 3 0]

def library : Library := fun id => if id < 75 then (if id < 37 then (if id < 18 then (if id < 9 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))))) else (if id < 13 then (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none))) else (if id < 15 then (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))))) else (if id < 27 then (if id < 22 then (if id < 20 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none))) else (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none))))) else (if id < 32 then (if id < 29 then (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none)) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)))) else (if id < 34 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))))))) else (if id < 56 then (if id < 46 then (if id < 41 then (if id < 39 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))) else (if id < 43 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))))) else (if id < 51 then (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none)))) else (if id < 53 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)))))) else (if id < 65 then (if id < 60 then (if id < 58 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 62 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none)) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none))))) else (if id < 70 then (if id < 67 then (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)))) else (if id < 72 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)))))))) else (if id < 113 then (if id < 94 then (if id < 84 then (if id < 79 then (if id < 77 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none))) else (if id < 81 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none))))) else (if id < 89 then (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)))) else (if id < 91 then (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none)) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)))))) else (if id < 103 then (if id < 98 then (if id < 96 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none))) else (if id < 100 then (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none)) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none))))) else (if id < 108 then (if id < 105 then (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none)))) else (if id < 110 then (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none)) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none))))))) else (if id < 132 then (if id < 122 then (if id < 117 then (if id < 115 then (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none)) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none))) else (if id < 119 then (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none)) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none))))) else (if id < 127 then (if id < 124 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none)))) else (if id < 129 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none)))))) else (if id < 141 then (if id < 136 then (if id < 134 then (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none)) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none))) else (if id < 138 then (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none)) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none))))) else (if id < 146 then (if id < 143 then (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none)) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none)))) else (if id < 148 then (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none)) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![6, 5, 2, 3, 1, 4], ![2, 6, 5, 3, 0, 4], ![1, 6, 5, 0, 3, 4], ![6, 5, 1, 0, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 3, 1, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 51 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15232)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![6, 5, 2, 3, 1, 4], ![6, 2, 5, 3, 0, 4], ![6, 1, 5, 0, 3, 4], ![6, 5, 1, 0, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 3, 1, 2, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 50 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15233)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![5, 2, 3, 1, 4, 6], ![5, 2, 3, 0, 4, 6], ![5, 1, 0, 3, 4, 6], ![5, 1, 0, 2, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 19 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15234)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![5, 2, 3, 1, 4, 6], ![5, 2, 3, 0, 4, 6], ![5, 1, 0, 3, 4, 6], ![5, 1, 0, 2, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 88 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15235)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![5, 2, 3, 1, 4, 6], ![5, 2, 3, 0, 4, 6], ![5, 1, 0, 3, 6, 4], ![5, 1, 0, 2, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 3, 2, 1, 0, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 143 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15236)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![5, 2, 3, 1, 4, 6], ![5, 2, 3, 0, 6, 4], ![5, 1, 0, 3, 6, 4], ![5, 1, 0, 2, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 2, 1, 0, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 136 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15237)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![5, 2, 3, 1, 6, 4], ![5, 2, 3, 0, 6, 4], ![5, 1, 0, 3, 6, 4], ![5, 1, 0, 2, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 15 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15238)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![5, 2, 3, 1, 4, 6], ![5, 2, 3, 0, 4, 6], ![5, 1, 0, 6, 3, 4], ![5, 1, 0, 6, 2, 4], ![5, 0, 1, 6, 2, 3], ![4, 3, 2, 1, 0, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 52 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15239)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![5, 2, 3, 1, 4, 6], ![5, 2, 3, 0, 6, 4], ![5, 1, 0, 6, 3, 4], ![5, 1, 0, 6, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 2, 1, 0, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 148 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15240)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![5, 2, 3, 1, 6, 4], ![5, 2, 3, 0, 6, 4], ![5, 1, 0, 6, 3, 4], ![5, 1, 0, 6, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 35 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15241)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![5, 2, 3, 6, 1, 4], ![5, 2, 3, 6, 0, 4], ![5, 1, 0, 3, 6, 4], ![5, 1, 0, 2, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 0, 2, 3, 5]], proof := .tail 110 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15242)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![5, 2, 3, 6, 1, 4], ![5, 2, 3, 6, 0, 4], ![5, 1, 0, 6, 3, 4], ![5, 1, 0, 6, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 0, 3, 2, 5]], proof := .tail 125 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15243)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![5, 2, 6, 3, 1, 4], ![5, 2, 3, 6, 0, 4], ![5, 1, 0, 6, 3, 4], ![5, 1, 6, 0, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 3, 0, 2, 5]], proof := .tail 62 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15244)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![5, 2, 6, 3, 1, 4], ![5, 2, 6, 3, 0, 4], ![5, 1, 0, 6, 3, 4], ![5, 6, 1, 0, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 3, 1, 0, 2, 5]], proof := .tail 125 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15245)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![5, 6, 2, 3, 1, 4], ![5, 2, 3, 6, 0, 4], ![5, 1, 6, 0, 3, 4], ![5, 1, 6, 0, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 3, 2, 0, 5]], proof := .tail 4 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15246)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![5, 6, 2, 3, 1, 4], ![5, 2, 6, 3, 0, 4], ![5, 1, 6, 0, 3, 4], ![5, 6, 1, 0, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 3, 1, 2, 0, 5]], proof := .tail 4 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15247)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![5, 6, 2, 3, 1, 4], ![5, 6, 2, 3, 0, 4], ![5, 6, 1, 0, 3, 4], ![5, 6, 1, 0, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 5]], proof := .tail 34 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15248)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 5, 2, 3, 1, 4], ![5, 2, 3, 6, 0, 4], ![5, 1, 6, 0, 3, 4], ![5, 1, 6, 0, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 1, 6, 0], ![4, 1, 3, 2, 5, 0]], proof := .tail 101 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15249)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![6, 5, 2, 3, 1, 4], ![5, 2, 6, 3, 0, 4], ![5, 1, 6, 0, 3, 4], ![5, 6, 1, 0, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 1, 6, 0], ![4, 3, 1, 2, 5, 0]], proof := .tail 101 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15250)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 5, 2, 3, 1, 4], ![5, 6, 2, 3, 0, 4], ![5, 6, 1, 0, 3, 4], ![5, 6, 1, 0, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 5, 0]], proof := .tail 20 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15251)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 5, 2, 3, 1, 4], ![6, 5, 2, 3, 0, 4], ![5, 6, 1, 0, 3, 4], ![5, 6, 1, 0, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 6, 1, 0], ![4, 3, 2, 5, 1, 0]], proof := .tail 49 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15252)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 5, 2, 3, 1, 4], ![6, 5, 2, 3, 0, 4], ![6, 5, 1, 0, 3, 4], ![5, 6, 1, 0, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 6, 2, 1, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 64 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15253)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![6, 5, 2, 3, 1, 4], ![6, 5, 2, 3, 0, 4], ![6, 5, 1, 0, 3, 4], ![6, 5, 1, 0, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 3, 2, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 141 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15254)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![6, 5, 2, 3, 1, 4], ![6, 5, 2, 3, 0, 4], ![6, 5, 1, 0, 3, 4], ![6, 5, 1, 0, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 3, 2, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 137 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15255)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 4, 3, 5, 6], ![1, 0, 4, 2, 5, 6], ![0, 1, 3, 2, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 45 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15256)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 4, 3, 5, 6], ![1, 0, 4, 2, 5, 6], ![0, 1, 3, 2, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 8 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15257)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 4, 3, 5, 6], ![1, 0, 4, 2, 6, 5], ![0, 1, 3, 2, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 56 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15258)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 4, 3, 6, 5], ![1, 0, 4, 2, 6, 5], ![0, 1, 3, 2, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 104 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15259)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 6, 5], ![1, 0, 4, 3, 6, 5], ![1, 0, 4, 2, 6, 5], ![0, 1, 3, 2, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .tail 67 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15260)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![2, 3, 1, 4, 6, 5], ![2, 3, 0, 4, 6, 5], ![1, 0, 4, 3, 6, 5], ![1, 0, 4, 2, 6, 5], ![0, 1, 3, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 67 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15261)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 4, 6, 3, 5], ![1, 0, 4, 6, 2, 5], ![0, 1, 3, 2, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 10 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15262)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 6, 4, 3, 5], ![1, 0, 4, 6, 2, 5], ![0, 1, 3, 6, 2, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 4, 2]], proof := .tail 11 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15263)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![0, 1, 6, 3, 2, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 4, 3, 2]], proof := .tail 142 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15264)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 6, 5], ![1, 0, 4, 6, 3, 5], ![1, 0, 4, 6, 2, 5], ![0, 1, 3, 2, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 3, 2, 4]], proof := .tail 16 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15265)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 6, 5], ![1, 0, 6, 4, 3, 5], ![1, 0, 4, 6, 2, 5], ![0, 1, 3, 6, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 3, 4, 2]], proof := .tail 11 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15266)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 6, 5], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![0, 1, 6, 3, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 4, 3, 2]], proof := .tail 13 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15267)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 6, 4, 5], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![0, 6, 1, 3, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 1, 3, 2]], proof := .tail 63 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15268)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![2, 3, 1, 4, 6, 5], ![2, 3, 0, 4, 6, 5], ![1, 0, 4, 6, 3, 5], ![1, 0, 4, 6, 2, 5], ![0, 1, 3, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 16 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15269)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![2, 3, 1, 4, 6, 5], ![2, 3, 0, 4, 6, 5], ![1, 0, 6, 4, 3, 5], ![1, 0, 4, 6, 2, 5], ![0, 1, 3, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 11 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15270)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![2, 3, 1, 4, 6, 5], ![2, 3, 0, 4, 6, 5], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![0, 1, 6, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 4, 3, 2]], proof := .tail 13 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15271)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![2, 3, 1, 4, 6, 5], ![2, 3, 0, 6, 4, 5], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![0, 6, 1, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 1, 3, 2]], proof := .tail 33 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15272)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![2, 3, 1, 6, 4, 5], ![2, 3, 0, 6, 4, 5], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![6, 0, 1, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 0, 1, 3, 2]], proof := .tail 100 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15273)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![2, 3, 6, 1, 4, 5], ![2, 3, 6, 0, 4, 5], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![6, 0, 1, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 0, 3, 2]], proof := .tail 0 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15274)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![2, 6, 3, 1, 4, 5], ![2, 3, 6, 0, 4, 5], ![1, 0, 6, 4, 3, 5], ![1, 6, 0, 4, 2, 5], ![6, 0, 1, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 3, 0, 2]], proof := .tail 48 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15275)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![2, 6, 3, 1, 4, 5], ![2, 6, 3, 0, 4, 5], ![1, 0, 6, 4, 3, 5], ![6, 1, 0, 4, 2, 5], ![6, 0, 1, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 120 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15276)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![6, 2, 3, 1, 4, 5], ![2, 3, 6, 0, 4, 5], ![1, 6, 0, 4, 3, 5], ![1, 6, 0, 4, 2, 5], ![6, 0, 1, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 48 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15277)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 2, 3, 1, 4, 5], ![2, 6, 3, 0, 4, 5], ![1, 6, 0, 4, 3, 5], ![6, 1, 0, 4, 2, 5], ![6, 0, 1, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 120 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15278)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 2, 3, 1, 4, 5], ![6, 2, 3, 0, 4, 5], ![6, 1, 0, 4, 3, 5], ![6, 1, 0, 4, 2, 5], ![6, 0, 1, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 112 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15279)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 4, 5, 3, 6], ![1, 0, 4, 5, 2, 6], ![0, 1, 3, 2, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 95 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15280)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 4, 5, 3, 6], ![1, 0, 4, 5, 2, 6], ![0, 1, 3, 2, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 55 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15281)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 4, 5, 6, 3], ![1, 0, 4, 5, 6, 2], ![0, 1, 3, 2, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 27 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15282)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 4, 5, 6, 3], ![1, 0, 4, 5, 6, 2], ![0, 1, 3, 2, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 28 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15283)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 4, 6, 5, 3], ![1, 0, 4, 5, 6, 2], ![0, 1, 3, 2, 6, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 132 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15284)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 4, 6, 5, 3], ![1, 0, 4, 6, 5, 2], ![0, 1, 3, 2, 6, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 107 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15285)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 6, 4, 5, 3], ![1, 0, 4, 5, 6, 2], ![0, 1, 3, 6, 2, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 4, 2]], proof := .tail 11 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15286)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 6, 4, 5, 3], ![1, 0, 4, 6, 5, 2], ![0, 1, 3, 6, 2, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 4, 2]], proof := .tail 11 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15287)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 2], ![0, 1, 6, 3, 2, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 4, 3, 2]], proof := .tail 147 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15288)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 6, 5], ![1, 0, 4, 6, 5, 3], ![1, 0, 4, 6, 5, 2], ![0, 1, 3, 2, 6, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 1, 3, 2, 4]], proof := .tail 80 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15289)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 6, 5], ![1, 0, 6, 4, 5, 3], ![1, 0, 4, 6, 5, 2], ![0, 1, 3, 6, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 1, 3, 4, 2]], proof := .tail 11 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15290)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 6, 5], ![1, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 2], ![0, 1, 6, 3, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 1, 4, 3, 2]], proof := .tail 134 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15291)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 6, 4, 5], ![1, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 2], ![0, 6, 1, 3, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 4, 1, 3, 2]], proof := .tail 25 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15292)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![2, 3, 1, 4, 6, 5], ![2, 3, 0, 4, 6, 5], ![1, 0, 4, 6, 5, 3], ![1, 0, 4, 6, 5, 2], ![0, 1, 3, 2, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 2, 4]], proof := .low6 (![53, 113, 61, 44, 91, 7, 31, 109, 127, 42, 58, 69, 111, 85, 70, 102, 128, 126, 29, 30, 135, 23, 150, 26, 42, 78, 22, 119]) }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15293)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![2, 3, 1, 4, 6, 5], ![2, 3, 0, 4, 6, 5], ![1, 0, 6, 4, 5, 3], ![1, 0, 4, 6, 5, 2], ![0, 1, 3, 6, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 11 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15294)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![2, 3, 1, 4, 6, 5], ![2, 3, 0, 4, 6, 5], ![1, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 2], ![0, 1, 6, 3, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 4, 3, 2]], proof := .tail 134 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15295)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![2, 3, 1, 4, 6, 5], ![2, 3, 0, 6, 4, 5], ![1, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 2], ![0, 6, 1, 3, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 4, 1, 3, 2]], proof := .tail 17 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15296)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![2, 3, 1, 6, 4, 5], ![2, 3, 0, 6, 4, 5], ![1, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 2], ![6, 0, 1, 3, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 0, 1, 3, 2]], proof := .low6 (![77, 76, 92, 2, 103, 36, 116, 18, 86, 79, 43, 81, 43, 73, 123, 139, 57, 5, 82, 47, 138, 105, 12, 129, 89, 94, 37, 24]) }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15297)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![2, 3, 6, 1, 4, 5], ![2, 3, 6, 0, 4, 5], ![1, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 2], ![6, 0, 1, 3, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 1, 0, 3, 2]], proof := .tail 46 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15298)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![2, 6, 3, 1, 4, 5], ![2, 3, 6, 0, 4, 5], ![1, 0, 6, 4, 5, 3], ![1, 6, 0, 4, 5, 2], ![6, 0, 1, 3, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 1, 3, 0, 2]], proof := .tail 90 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15299)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![2, 6, 3, 1, 4, 5], ![2, 6, 3, 0, 4, 5], ![1, 0, 6, 4, 5, 3], ![6, 1, 0, 4, 5, 2], ![6, 0, 1, 3, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 97 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15300)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![6, 2, 3, 1, 4, 5], ![2, 3, 6, 0, 4, 5], ![1, 6, 0, 4, 5, 3], ![1, 6, 0, 4, 5, 2], ![6, 0, 1, 3, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 90 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15301)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![6, 2, 3, 1, 4, 5], ![2, 6, 3, 0, 4, 5], ![1, 6, 0, 4, 5, 3], ![6, 1, 0, 4, 5, 2], ![6, 0, 1, 3, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 97 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15302)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![6, 2, 3, 1, 4, 5], ![6, 2, 3, 0, 4, 5], ![6, 1, 0, 4, 5, 3], ![6, 1, 0, 4, 5, 2], ![6, 0, 1, 3, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 83 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15303)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 5, 4, 3, 6], ![1, 0, 4, 5, 2, 6], ![0, 1, 3, 5, 2, 6], ![0, 1, 3, 4, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 21 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15304)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 5, 4, 6, 3], ![1, 0, 4, 5, 6, 2], ![0, 1, 3, 5, 2, 6], ![0, 1, 3, 4, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 21 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15305)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 5, 6, 4, 3], ![1, 0, 4, 5, 6, 2], ![0, 1, 3, 5, 6, 2], ![0, 1, 3, 4, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 98 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15306)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 6, 5, 4, 3], ![1, 0, 4, 5, 6, 2], ![0, 1, 3, 5, 6, 2], ![0, 1, 3, 4, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 60 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15307)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 6, 5, 4, 3], ![1, 0, 4, 5, 6, 2], ![0, 1, 3, 6, 5, 2], ![0, 1, 3, 6, 4, 2], ![0, 1, 3, 5, 4, 2]], proof := .tail 146 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15308)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 6, 5, 4, 3], ![1, 0, 4, 6, 5, 2], ![0, 1, 3, 6, 5, 2], ![0, 1, 6, 3, 4, 2], ![0, 1, 5, 3, 4, 2]], proof := .tail 121 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15309)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 4, 5, 2], ![0, 1, 6, 3, 5, 2], ![0, 1, 6, 3, 4, 2], ![0, 1, 5, 4, 3, 2]], proof := .tail 118 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15310)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 6, 5], ![1, 0, 6, 5, 4, 3], ![1, 0, 4, 6, 5, 2], ![0, 1, 3, 6, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 1, 3, 4, 2]], proof := .tail 66 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15311)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 6, 5], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 4, 5, 2], ![0, 1, 6, 3, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 1, 4, 3, 2]], proof := .tail 93 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15312)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 6, 4, 5], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 4, 5, 2], ![0, 6, 1, 3, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 4, 1, 3, 2]], proof := .tail 1 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15313)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![2, 3, 1, 4, 6, 5], ![2, 3, 0, 4, 6, 5], ![1, 0, 6, 5, 4, 3], ![1, 0, 4, 6, 5, 2], ![0, 1, 3, 6, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 1, 3, 4, 2]], proof := .tail 66 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15314)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![2, 3, 1, 4, 6, 5], ![2, 3, 0, 4, 6, 5], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 4, 5, 2], ![0, 1, 6, 3, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 1, 4, 3, 2]], proof := .tail 93 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15315)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![2, 3, 1, 4, 6, 5], ![2, 3, 0, 6, 4, 5], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 4, 5, 2], ![0, 6, 1, 3, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 4, 1, 3, 2]], proof := .tail 40 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15316)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![2, 3, 1, 6, 4, 5], ![2, 3, 0, 6, 4, 5], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 4, 5, 2], ![6, 0, 1, 3, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 4, 0, 1, 3, 2]], proof := .tail 39 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15317)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![2, 3, 6, 1, 4, 5], ![2, 3, 6, 0, 4, 5], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 4, 5, 2], ![6, 0, 1, 3, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 4, 1, 0, 3, 2]], proof := .tail 122 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15318)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![2, 6, 3, 1, 4, 5], ![2, 3, 6, 0, 4, 5], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 4, 5, 2], ![6, 0, 1, 3, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 4, 1, 3, 0, 2]], proof := .tail 145 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15319)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![2, 6, 3, 1, 4, 5], ![2, 6, 3, 0, 4, 5], ![1, 0, 6, 5, 4, 3], ![6, 1, 0, 4, 5, 2], ![6, 0, 1, 3, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 130 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15320)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![6, 2, 3, 1, 4, 5], ![2, 3, 6, 0, 4, 5], ![1, 6, 0, 5, 4, 3], ![1, 6, 0, 4, 5, 2], ![6, 0, 1, 3, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 4, 1, 3, 2, 0]], proof := .tail 145 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15321)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![6, 2, 3, 1, 4, 5], ![2, 6, 3, 0, 4, 5], ![1, 6, 0, 5, 4, 3], ![6, 1, 0, 4, 5, 2], ![6, 0, 1, 3, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 130 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15322)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![6, 2, 3, 1, 4, 5], ![6, 2, 3, 0, 4, 5], ![6, 1, 0, 5, 4, 3], ![6, 1, 0, 4, 5, 2], ![6, 0, 1, 3, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 96 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15323)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 5, 4, 3, 6], ![1, 0, 5, 4, 2, 6], ![0, 1, 5, 3, 2, 6], ![0, 1, 4, 3, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 6 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15324)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 5, 4, 6, 3], ![1, 0, 5, 4, 6, 2], ![0, 1, 5, 3, 2, 6], ![0, 1, 4, 3, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 124 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15325)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 5, 6, 4, 3], ![1, 0, 5, 4, 6, 2], ![0, 1, 5, 3, 6, 2], ![0, 1, 4, 3, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 65 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15326)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 2], ![0, 1, 5, 6, 3, 2], ![0, 1, 4, 3, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 68 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15327)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 6, 5, 4, 3], ![1, 0, 5, 4, 6, 2], ![0, 1, 5, 3, 6, 2], ![0, 1, 4, 3, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 117 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15328)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 6, 5, 4, 3], ![1, 0, 5, 6, 4, 2], ![0, 1, 5, 6, 3, 2], ![0, 1, 4, 3, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 60 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15329)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![0, 1, 5, 6, 3, 2], ![0, 1, 4, 6, 3, 2], ![0, 1, 4, 5, 3, 2]], proof := .tail 144 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15330)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 5, 6], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![0, 1, 6, 5, 3, 2], ![0, 1, 6, 4, 3, 2], ![0, 1, 5, 4, 3, 2]], proof := .tail 99 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15331)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 4, 6, 5], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![0, 1, 6, 5, 3, 2], ![0, 6, 1, 4, 3, 2], ![0, 5, 1, 4, 3, 2]], proof := .tail 3 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15332)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 6, 4, 5], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![0, 6, 1, 5, 3, 2], ![0, 6, 1, 4, 3, 2], ![0, 5, 4, 1, 3, 2]], proof := .tail 41 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15333)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![2, 3, 1, 4, 6, 5], ![2, 3, 0, 4, 6, 5], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![0, 1, 6, 5, 3, 2], ![6, 0, 1, 4, 3, 2], ![5, 0, 1, 4, 3, 2]], proof := .tail 3 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15334)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![2, 3, 1, 4, 6, 5], ![2, 3, 0, 6, 4, 5], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![0, 6, 1, 5, 3, 2], ![6, 0, 1, 4, 3, 2], ![5, 0, 4, 1, 3, 2]], proof := .tail 54 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15335)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![2, 3, 1, 6, 4, 5], ![2, 3, 0, 6, 4, 5], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![6, 0, 1, 5, 3, 2], ![6, 0, 1, 4, 3, 2], ![5, 4, 0, 1, 3, 2]], proof := .tail 140 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15336)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![2, 3, 6, 1, 4, 5], ![2, 3, 6, 0, 4, 5], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![6, 0, 1, 5, 3, 2], ![6, 0, 1, 4, 3, 2], ![5, 4, 1, 0, 3, 2]], proof := .tail 72 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15337)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![2, 6, 3, 1, 4, 5], ![2, 3, 6, 0, 4, 5], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 5, 4, 2], ![6, 0, 1, 5, 3, 2], ![6, 0, 1, 4, 3, 2], ![5, 4, 1, 3, 0, 2]], proof := .tail 131 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15338)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![2, 6, 3, 1, 4, 5], ![2, 6, 3, 0, 4, 5], ![1, 0, 6, 5, 4, 3], ![6, 1, 0, 5, 4, 2], ![6, 0, 1, 5, 3, 2], ![6, 0, 1, 4, 3, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 114 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15339)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 2, 3, 1, 4, 5], ![2, 3, 6, 0, 4, 5], ![1, 6, 0, 5, 4, 3], ![1, 6, 0, 5, 4, 2], ![6, 0, 1, 5, 3, 2], ![6, 0, 1, 4, 3, 2], ![5, 4, 1, 3, 2, 0]], proof := .tail 9 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15340)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 2, 3, 1, 4, 5], ![2, 6, 3, 0, 4, 5], ![1, 6, 0, 5, 4, 3], ![6, 1, 0, 5, 4, 2], ![6, 0, 1, 5, 3, 2], ![6, 0, 1, 4, 3, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 114 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15341)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 2, 3, 1, 4, 5], ![6, 2, 3, 0, 4, 5], ![6, 1, 0, 5, 4, 3], ![6, 1, 0, 5, 4, 2], ![6, 0, 1, 5, 3, 2], ![6, 0, 1, 4, 3, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 75 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15342)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 5, 4, 6], ![1, 0, 5, 4, 3, 6], ![1, 0, 5, 4, 2, 6], ![0, 5, 1, 3, 2, 6], ![0, 4, 1, 3, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 106 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15343)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 5, 4, 6], ![1, 0, 5, 4, 6, 3], ![1, 0, 5, 4, 6, 2], ![0, 5, 1, 3, 2, 6], ![0, 4, 1, 3, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 87 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15344)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 5, 4, 6], ![1, 0, 5, 6, 4, 3], ![1, 0, 5, 4, 6, 2], ![0, 5, 1, 3, 6, 2], ![0, 4, 1, 3, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 38 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15345)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 5, 4, 6], ![1, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 2], ![0, 5, 1, 6, 3, 2], ![0, 4, 1, 3, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 133 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15346)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 5, 4, 6], ![1, 0, 6, 5, 4, 3], ![1, 0, 5, 4, 6, 2], ![0, 5, 1, 3, 6, 2], ![0, 4, 1, 3, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 115 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15347)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 5, 4, 6], ![1, 0, 6, 5, 4, 3], ![1, 0, 5, 6, 4, 2], ![0, 5, 1, 6, 3, 2], ![0, 4, 1, 3, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 133 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15348)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 5, 4, 6], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![0, 5, 1, 6, 3, 2], ![0, 4, 1, 6, 3, 2], ![0, 1, 4, 5, 3, 2]], proof := .tail 149 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15349)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 5, 6, 4], ![1, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 1, 3, 2, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 14 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15350)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 5, 6, 4], ![1, 0, 6, 5, 4, 3], ![1, 0, 5, 6, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 1, 3, 6, 2], ![0, 4, 1, 3, 5, 2]], proof := .tail 108 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15351)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 5, 6, 4], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 1, 6, 3, 2], ![0, 4, 1, 5, 3, 2]], proof := .tail 59 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15352)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 6, 5, 4], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 6, 1, 3, 2], ![0, 4, 5, 1, 3, 2]], proof := .tail 59 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15353)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![2, 3, 1, 4, 5, 6], ![2, 3, 0, 6, 5, 4], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![0, 6, 5, 1, 3, 2], ![0, 6, 4, 1, 3, 2], ![0, 5, 4, 1, 3, 2]], proof := .tail 32 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15354)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![2, 3, 1, 4, 6, 5], ![2, 3, 0, 6, 5, 4], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![0, 6, 5, 1, 3, 2], ![6, 0, 4, 1, 3, 2], ![5, 0, 4, 1, 3, 2]], proof := .tail 84 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15355)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![2, 3, 1, 6, 4, 5], ![2, 3, 0, 6, 5, 4], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![6, 0, 5, 1, 3, 2], ![6, 0, 4, 1, 3, 2], ![5, 4, 0, 1, 3, 2]], proof := .tail 140 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15356)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![2, 3, 6, 1, 4, 5], ![2, 3, 6, 0, 5, 4], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![6, 0, 5, 1, 3, 2], ![6, 0, 4, 1, 3, 2], ![5, 4, 1, 0, 3, 2]], proof := .tail 140 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15357)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![2, 6, 3, 1, 4, 5], ![2, 3, 6, 0, 5, 4], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 5, 4, 2], ![6, 0, 5, 1, 3, 2], ![6, 0, 4, 1, 3, 2], ![5, 4, 1, 3, 0, 2]], proof := .tail 74 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15358)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![2, 6, 3, 1, 4, 5], ![2, 6, 3, 0, 5, 4], ![1, 0, 6, 5, 4, 3], ![6, 1, 0, 5, 4, 2], ![6, 0, 5, 1, 3, 2], ![6, 0, 4, 1, 3, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 71 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 15359)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (15232 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 15232 ≤ id.val) (hhigh : id.val < 15360) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 15232)) = true := by
  let j : Fin 128 := ⟨id.val - 15232, by omega⟩
  have hsum : 15232 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (15232 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard119
