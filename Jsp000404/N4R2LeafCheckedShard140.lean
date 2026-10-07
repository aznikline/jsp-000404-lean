import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard140
open N4R2RowDataReplay

-- Original cycle 030c210d9c7c7d53bbb9c3d468ac6d38c6e421e5540483eb5f0b15fb2dadf397; original global index 244.
def localCycle00000 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 6, .distance 3 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![4, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 11 2, .gapLower 6 3, .triangle 21 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 03ebbf996e97d765a690b240d1c3b23246539a91837f2d1125065be63dc8e630; original global index 310.
def localCycle00001 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 22 0, .triangle 23 0, .corridorLower 4 6]

-- Original cycle 051023e6f59de191a1bce5969e4252fe48f1a7f87c733255d94e96fd34de02cf; original global index 408.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 11 2, .gapLower 6 2, .triangle 23 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 061dfbd8e51f32209bf2880a858cc1d1a26ef13d6b5ceb09b63afbc2fa9e6c54; original global index 505.
def localCycle00003 : Cycle where
  length := 3
  data := {
    node := ![.theta 0, .distance 0 1, .theta 1, .theta 0]
    constant := ![2, -2, 0]
    coefficient := ![1, -1, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 6, .gapUpper 1 6, .thetaNext 0]

-- Original cycle 06c882c2198a1cc45a9fcc69f71d9ed7ab18bc329cbd00768b995bf0652ecc7b; original global index 557.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 6, .distance 0 2, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 12 2, .gapLower 0 3, .triangle 11 2, .gapLower 0 1, .gapLower 2 1, .corridorLower 1 2]

-- Original cycle 07156a8f99698fefdf487256773e080ee9dd884d4b21cb607b31a8a0a09dbe97; original global index 583.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 10 0, .triangle 11 0, .triangle 21 2, .triangle 24 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 0871e7124286714f68d278ad4f6a3b0281210b71d6a21313ab4ba3aa6701ae67; original global index 673.
def localCycle00006 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 08a72bef1c7a799d6f9eed9151a782fea57fe756373fd700732fc3f5f8eb3d0b; original global index 690.
def localCycle00007 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 2, .gapLower 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 0912ca98d21481b8bfb59c35010166a1913762f8445e364b9d068a464b53a9fd; original global index 724.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -3, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 4 1, .triangle 21 1, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 0990296b574cd7ab83d794d8e373fd4baeeb016a444f62643fee3becb380a411; original global index 762.
def localCycle00009 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 3 6, .distance 4 6, .distance 0 6, .distance 1 6, .distance 1 4, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 32 1, .gapLower 6 2, .triangle 4 1, .triangle 23 1, .gapLower 4 0]

-- Original cycle 09ca555010576b0ff1c3fa93f690e3c0a81646256f5d3aa231259af6e86f7fc9; original global index 785.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 2, .gapLower 6 3, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 09fdfad90aea58dc3a005958932b8a01c02548966ad00512438d3f6580cc331c; original global index 803.
def localCycle00011 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 0c80827b77617bb33757fa86e671f3ef5c83ddf730ca84f21e612abaca4e4e1e; original global index 990.
def localCycle00012 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .gapLower 6 0]

-- Original cycle 0c8bd5c71b94c4724322fce4a26c8c9ad699afcfef29a92e3b137fe32213ddee; original global index 993.
def localCycle00013 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .triangle 8 2, .triangle 4 1, .gapLower 6 1, .gapLower 6 0]

-- Original cycle 0d8ea2843638216feccd7d2e9249ece36b66e87a25b2c248b73090eefce33206; original global index 1072.
def localCycle00014 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 1, -2, 0, 3, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapUpper 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 0e1c7881ae1c00fc529f650e4478fb60a1263e2b941655789a33c0eb21475fb1; original global index 1113.
def localCycle00015 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 6, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -2, -2, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.triangle 2 2, .triangle 13 2, .gapLower 6 2, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle 0e8ca9ea15a287cf4c98afb8eb09dde332003b2cac79c151e40c52d8de86f438; original global index 1149.
def localCycle00016 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 0f0a145bd3c0b1c54652674226a4c102f4e6e2f05f720680920ce884040ddbb4; original global index 1194.
def localCycle00017 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 2 1, .triangle 22 0, .corridorLower 4 5]

-- Original cycle 0f0a2b3e65328817f481f77d49c6e4f30adee554b2fee67e3ef4a15c17ac7741; original global index 1195.
def localCycle00018 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 0 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .gapLower 2 4, .gapLower 3 3, .triangle 10 0, .triangle 31 1, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 0f2c6674fafa7f47594fdebb9a423f0696235e5cdf063bfe779e4b70e205f7d0; original global index 1208.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .gapLower 4 3, .triangle 13 0, .triangle 23 0, .gapLower 4 0]

-- Original cycle 0ff72f9166246487daa56f68b87f1bbb45868f230da7f53a1031bf8a6d984802; original global index 1273.
def localCycle00020 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 0 2, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 0, .triangle 7 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 141bd0687b1f1d02ee17eb54ca1aea8390a49139a99e588f666ab0a46aec0c40; original global index 1589.
def localCycle00021 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 22 0, .triangle 23 0, .corridorLower 4 6]

-- Original cycle 14f06f037bb3ccf248859a90337e6ee2de94b09ba9b5ea8335a8e39a8442397c; original global index 1662.
def localCycle00022 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 1 3, .theta 3]
    constant := ![4, 0, -2, -2, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 11 1, .triangle 10 0, .triangle 20 0, .gapLower 3 0]

-- Original cycle 1531b181ae36b67d548ad68acf6e55e5e96aae0957d4a2e3f77e01d79f5c5c39; original global index 1678.
def localCycle00023 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 16d92797fd6df4ae24f5a43792fb52554be93b794b8ceaec26b68a235abefe11; original global index 1797.
def localCycle00024 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 11 2, .triangle 13 1, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 17021928f6245eed9ac2d98fafb79ec6c3635eb56d0555f4f7664f38e13ec194; original global index 1811.
def localCycle00025 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 4, .distance 0 3, .distance 0 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .theta 0]
    constant := ![2, 0, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.gapLower 0 6, .triangle 2 2, .triangle 9 1, .gapLower 0 2, .triangle 11 1, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0]

-- Original cycle 17d5579bbd60659f2ec2107d5e095f6f6145d57abd6eeb09128707af07134653; original global index 1862.
def localCycle00026 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 8 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 17da6efed2e685c9e736e02fd7cc360750cf9a897573d824471ad5b4a9ae7230; original global index 1865.
def localCycle00027 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 1978b20d83a919a5b10ddc8eb2d853394342d3e9320403eba5664fbb66fd29c0; original global index 1988.
def localCycle00028 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 4 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 23 2, .gapLower 6 0]

-- Original cycle 197f656ef60a597694aa838bc9bef9ff219dd2e6c1764b9e61736e4aa69164ff; original global index 1989.
def localCycle00029 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 1a84285cea27a5016e06077ad1bc937cc6acfd5da06492664228d045e7413986; original global index 2064.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 9 1, .triangle 11 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0]

-- Original cycle 1aa6b20604052f59facdc3e293e44bf7756f462417e47d9d3f58520097cdcee3; original global index 2073.
def localCycle00031 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![4, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 0, .triangle 27 0, .triangle 21 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 1b9845321525659c5bd04dcdcaf5f76d56c0270457918bb115b9bab9c6d56e6e; original global index 2132.
def localCycle00032 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 9 1, .triangle 11 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 1d8fd2976a5788e5c4a2ed99e02c96788139f2662af7769c104e5e01807c3bbe; original global index 2273.
def localCycle00033 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .theta 6, .distance 5 6, .distance 3 6, .distance 2 3, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -2, 2, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 2, .gapLower 6 0, .gapLower 6 6, .triangle 33 2, .triangle 27 0, .triangle 5 2, .triangle 10 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 1e5365a31d038231c9c57fd3ca28301ba474220051faadad543423041bff3c50; original global index 2331.
def localCycle00034 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 2, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 1e8d267cac6d2a6d35246ef957a488cef295f3c36796162f12f202e7214c4b73; original global index 2346.
def localCycle00035 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 8 2, .gapLower 6 2, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 1ef387a09220b33bb82ff36725423ce852d2c9713ea147d4fa515344bf88a76c; original global index 2378.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 1f675583dccbcb48fa91d560b68dacfd6562895f11bc81ff293c761b9e17e96e; original global index 2409.
def localCycle00037 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 2010c24a1333eed78c565e9d8a15dbd6b8a3a3c454686974535ba855f1e4d136; original global index 2461.
def localCycle00038 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 21bff1d75cdc5321172f0e336ed2ee2870d5a0932dfb4695d8c7a6c040cf2ad8; original global index 2588.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 29 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 22174f49fbfe4e74094d82ce6fab624360076d6e1a0509b12f4bd58619d33473; original global index 2610.
def localCycle00040 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 26 0, .triangle 10 2, .triangle 12 1, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 242dbc0ec76d096c7a44b49f1c6cd0a94853a4aafc35788d5c2aa83d126d9b1f; original global index 2774.
def localCycle00041 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 255e048078b534cf3c0ccd63be909504a728e5920cce817c77145c5693db6476; original global index 2875.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 11 2, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 26b2496d137dc699393aef3e7498646bbb131aa48e9efb5b412d527b0cc337bf; original global index 2965.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 14 2, .gapLower 6 2, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 26f23cdf179a6dd252081002d8bf813f3e247fbdf0e98d17c3201baa01c96b60; original global index 2985.
def localCycle00044 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 27 1, .triangle 26 0, .triangle 31 1, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 283ed0ba17b3bfa8d559c0c9a3293e54d6306810733e09f791cc84da89769aa5; original global index 3083.
def localCycle00045 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 11 1, .triangle 21 2, .triangle 23 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 2bd1c648861179db09d52db70f10b0617d801ac11c12892f74dd525921b5e8d7; original global index 3354.
def localCycle00046 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 2ceed90869a03b9971a16aabef349b8db1612714cc640a2794608abeb9d1e58f; original global index 3431.
def localCycle00047 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 11 2, .gapLower 6 2, .triangle 23 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 2ecd64253981134a4a55340c265b77c9e83ec56af0ac3e23468951bc9942cff7; original global index 3581.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![4, -1, -1, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 25 0, .triangle 27 0, .gapLower 6 3, .gapLower 6 2, .triangle 23 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 2f21ff58d33f74a8ae10865437877b9d406b02a56bc91f2c39d54eff91543ab3; original global index 3604.
def localCycle00049 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .triangle 8 2, .gapLower 6 2, .triangle 23 1, .gapLower 6 0]

-- Original cycle 2f69651f9b3e16fbba046a45f4bb9233acf1aa62efb6264cc4d305efc6a53015; original global index 3625.
def localCycle00050 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 300d8e9e1643621a77a7fffc049e8a2c8761d7adef31352983e55fbfa4703f99; original global index 3662.
def localCycle00051 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 30406780557f7d32cb80e076280f7ef8fb6cbb40ac2c37e8f191ea50d3c686a4; original global index 3672.
def localCycle00052 : Cycle where
  length := 3
  data := {
    node := ![.theta 0, .distance 0 1, .theta 1, .theta 0]
    constant := ![1, -2, 0]
    coefficient := ![1, -1, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 6, .gapUpper 1 6, .thetaNext 0]

-- Original cycle 304301f493f3674b72c3e2162df5835a0ce78393af680d3f1cf34a7ede376603; original global index 3674.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 319fffc1c287d8f7408fd362af23c5910e5fcfc716b08c0ef65db1f6dd56b9ad; original global index 3790.
def localCycle00054 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![-2, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 5, .gapLower 0 4, .gapLower 5 3, .triangle 22 2, .gapUpper 1 5]

-- Original cycle 327c695c2540c151ac03abe84c53385b56f1812339be6fcff4409c2438a4ef1f; original global index 3861.
def localCycle00055 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 35123bd7a5c4f587570e401b7f707372c5073bf8e3dfa8ef4977b866b12a8ddf; original global index 4059.
def localCycle00056 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Original cycle 3522ee338b2e58a767fd45276cc182ecc64060e80d8bfe62aef9597612fa2a74; original global index 4064.
def localCycle00057 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 2, .triangle 24 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 353c9a8710412b04fd8937bcbb9bc951ff1c78a764eb1bfc9d5482d0a491659f; original global index 4074.
def localCycle00058 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 5 2, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 37285485124530ccc70ec42f4d682cf2f23682fc73015d2b9b763218714aa475; original global index 4233.
def localCycle00059 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 3965e5b7601333fddb11fe4432dee870ebf8985b13fee5ee3389e1e2846a4799; original global index 4420.
def localCycle00060 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -2, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 12 2, .gapLower 0 3, .triangle 11 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 3991456845272a216566985cd914eb6c3e8f17fab62a543e7a41cb104b680fd1; original global index 4435.
def localCycle00061 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 20 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 39d05c78c9f295a1c67e02ccf1476bf6ca68819f245d8207c5b2739f139f173c; original global index 4462.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 6 2, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 3a1ad8e6baed0cfeb97d88b7641359317c4f7efb539ce469857c163afe036c50; original global index 4482.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, -2, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 1, .triangle 21 1, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 3b06ad2d86b9d10a5cf79e675dc3fc0a863f3a47067e510c14dd03cece0760c8; original global index 4559.
def localCycle00064 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 2 6, .distance 2 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .triangle 27 1]

-- Original cycle 3bcc6240f5d0822f2557faa1bab006e558ef92e8508e07daa6ec18f5190aa7fd; original global index 4627.
def localCycle00065 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![3, -1, -1, -2, 2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .gapLower 6 0, .gapLower 6 6, .triangle 30 0, .triangle 17 0, .corridorLower 1 2]

-- Original cycle 3d15b5c54f29baddec3ebeb5bb316bfc26222537a81a33e4020494d76446d0b9; original global index 4735.
def localCycle00066 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 6, .distance 3 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 2, .gapLower 6 3, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 3d6cadad86822adccaca46989575f8bb814f87122b87c63890ae045edf71e4cf; original global index 4757.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -2, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Original cycle 3f7bcb7ef36ebf1b72c1887e5006af82e90321a0fa802cc0f15cafa167b10609; original global index 4906.
def localCycle00068 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 3fc4df47408372851dc5aff192c0e4bba10372dbc14b2cda6935effb78298686; original global index 4925.
def localCycle00069 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 3, .triangle 13 1, .triangle 34 1, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 4178e7cd18124ad4c9562862612ba92791b042d0cef5b6bad08fb5b1b7c8837e; original global index 5051.
def localCycle00070 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .theta 6, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, -1, -1, -2, 2, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .gapLower 6 0, .gapLower 6 6, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 424e8413cd3a008f177fcbb1dbc7713f47b0e750d9710335d1e7e9c0963e94f2; original global index 5107.
def localCycle00071 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 2, .triangle 22 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 4385b4d741663a1e849efd165bb37379ded1d79995ab8c08fb65b21d63b2e7f1; original global index 5219.
def localCycle00072 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 4 6, .theta 4, .zero]
    constant := ![0, 2, 0, -1, -1, -1, 0, -1, 3, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .gapLower 6 1, .corridorLower 4 6, .thetaLower 4]

-- Original cycle 46a0a341ec81619f7981b45eba860dd4f5b3ead704031b99e46c25fe88137777; original global index 5465.
def localCycle00073 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 0 6, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3]
    constant := ![0, -2, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true] }
  origin := ![.triangle 11 2, .gapLower 6 3, .triangle 32 1, .gapUpper 4 3, .triangle 9 1]

-- Original cycle 471bea08cc2880980fb2b142a6c76210dc270fa10e680209554e6020a277f9df; original global index 5513.
def localCycle00074 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![-3, 0, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 5, .gapLower 4 3, .gapLower 5 2, .gapUpper 1 5]

-- Original cycle 48fdf1a6fe6964236459376354d24cf3b81043ee345b159c59e10da7b5baac5a; original global index 5652.
def localCycle00075 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 49d715e36b628b6efe15e59a316d4ab3e542ddaf1521a79d7ae47443a8a6c025; original global index 5725.
def localCycle00076 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 49e5c9c4f44d09c3d3785566479658c1a53e87a396b0afc0323ec81fd3404429; original global index 5732.
def localCycle00077 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 1, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 49ea364941d5b3fb1acd8574c2caf7d5a1112c1e1133ff05c7619581389e0010; original global index 5735.
def localCycle00078 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 11 2, .triangle 13 1, .triangle 23 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 49f2964308aee0245816aa8e3484f8e1a7ccfcfb1ce6741d374b4943eed64a05; original global index 5740.
def localCycle00079 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 4, .distance 0 6, .distance 1 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -3, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 2, .triangle 13 2, .gapLower 6 2, .triangle 21 1, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 4ad53b42f58044c8eb21fafc069c98be60fd2a838522bbb6dbe239bc933f83b2; original global index 5810.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 4 0]

-- Original cycle 4b0e962fedb6a9f9ed9cb43e8eec3a3cbc266f95f425880cc44a7ae8fc821387; original global index 5825.
def localCycle00081 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 4ba27aa621112081b7c8bb120915da3f67597a6fcc4868a71f5bc0a74412f782; original global index 5869.
def localCycle00082 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 3, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 27 0, .triangle 5 2, .triangle 10 0, .triangle 20 0, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 4d126b210a6ffb0f9cabe9641c1d2de09b865fc3b6fa637f241b9781aa8cf7b6; original global index 5986.
def localCycle00083 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 4e38ef35c9ecf49f91ea9e35db8d0c5b1858d26d15775d547cc0938a6bd4f7ba; original global index 6073.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 4e681af0a7f409b037dff311c4eaec6cad961de9865986f14c943c6701cc676f; original global index 6088.
def localCycle00085 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 23 0, .gapLower 4 0]

-- Original cycle 4fb1a09708104dddf2ce31c914e8c6c3a68ed6305b78797ea9e6d53177fdbda9; original global index 6188.
def localCycle00086 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 27 1, .triangle 26 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 4ff183a4951005fca814222b66a967e466c596d82d20848c94807efc85464553; original global index 6207.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 4ff1e5a4586dd04492a8ba167d688083b02183c0eef9f2506c26867b5de65208; original global index 6208.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .gapLower 6 3, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 502a6213e24cfc3ca87114bf4722e03d67d71c3e69f95dd401c8966cdd16f1f7; original global index 6221.
def localCycle00089 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 13 1, .triangle 23 0, .gapLower 4 0]

-- Original cycle 5053658bc332fed51eef185e4f834f57e615c84f55e828f0bcd1db1514b9a13d; original global index 6236.
def localCycle00090 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 11 0, .triangle 10 0, .triangle 20 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 51768a02414f1e33d52572871513b0f6dbabd654f665be4deceacd7d97cdc82b; original global index 6335.
def localCycle00091 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, true, true, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 13 2, .gapLower 6 1, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 525a311013a5ea2aff0049562af7d3e115b6d887e7ac4d8a4848de1eb1d0f1fb; original global index 6403.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -2, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .triangle 34 1, .gapLower 4 0]

-- Original cycle 52ab866aacf7887e45da17144cde3b1fd5cc895ebb61c59e33dbfd44a174f98c; original global index 6425.
def localCycle00093 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 54a6a655edf28dc73910846154469f3d89bbdab5d935b58500e72a625fee2add; original global index 6558.
def localCycle00094 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 4 6, .theta 6, .theta 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, -1, 0, -2, -2, 0, 0, 3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 54d458e1b98739db4d6d180c4004d40ad99c8819b2919a5ebd2b9614a1875087; original global index 6570.
def localCycle00095 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 5501bb230f6302edbfc7694642175588a973baec2d11e33a16f99f8aff006728; original global index 6581.
def localCycle00096 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 27 1, .triangle 26 0, .triangle 31 1, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 553725f638f81c0febd585ffbbe34b827088dfc2c9ec88a0f34d711438def3e7; original global index 6598.
def localCycle00097 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 25 0, .triangle 26 0, .triangle 10 0, .triangle 11 0, .triangle 21 0, .gapLower 3 0]

-- Original cycle 553e34b80fa6cfc0f755944c7d1ed113654d2c963e59c708a8bf67d828f91c3c; original global index 6599.
def localCycle00098 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 13 2, .gapLower 6 2, .gapUpper 4 3]

-- Original cycle 55db6f0fdcae427124fe67ab3d548d91d695c9b371697b7b781f62d115f279a5; original global index 6657.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 4, .distance 0 6, .distance 1 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 2, .triangle 13 2, .gapLower 6 2, .triangle 21 1, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 55f33d81c6f7dbe415c89ff61c77a9785a53111a25a0acef4ef90641d0ae999a; original global index 6665.
def localCycle00100 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 4, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![4, -1, 0, -2, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .gapLower 6 3, .triangle 13 1, .triangle 23 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 592c979471e620bbcc5f695e3f0e20e413ab0beaf84c932976450b7ca132ace0; original global index 6916.
def localCycle00101 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Original cycle 5baababcfa103b932bd52ef350e14fcc1f622a692ce3ebecf3346e52741a9407; original global index 7127.
def localCycle00102 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -2, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 11 1, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 5c3634b03edb351e2bc966ffeaf0d1480b1587e6975bc735fa758aa02304d668; original global index 7180.
def localCycle00103 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .gapLower 2 4, .triangle 26 0, .triangle 31 1, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 5d55893ad11fd6ee90f150addba03e059bd1cb7b93d236bad4fe70bd87d46365; original global index 7264.
def localCycle00104 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 5fb7245df6da0bad9d1eaf1d9da1128d94773243271bd8aa18346a4e57e7eb58; original global index 7454.
def localCycle00105 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, -2, 0, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, true, true, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .gapLower 6 2, .gapLower 6 1, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 60fea36eae943aab9a32bb83636de207f679238e3ee83e6429e94f8b11df6149; original global index 7558.
def localCycle00106 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 8 2, .gapLower 6 3, .triangle 21 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 610e2021c1028985eb66559c2f511c24b94231c1f5486fdd8fded954d8c2221e; original global index 7570.
def localCycle00107 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![4, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 11 0, .triangle 21 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 61e6aa8c3855ffc1d94c51d5a7d01abf9f3347020fa28506f0e00251b1a502fe; original global index 7643.
def localCycle00108 : Cycle where
  length := 15
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .theta 6, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -2, 2, 0, -1, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 2, .gapLower 6 0, .gapLower 6 6, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 10 2, .triangle 12 1, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 651b51271a4c10bff7177c3c1b5b4cde8315fd63576d9cadd78ceb3be3b56ea1; original global index 7867.
def localCycle00109 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, -1, -1, -2, 3, 0, 0, -2, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 11 1, .triangle 10 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 6548ad86c319edff71df5eddeee8efb1f2fdbc37eb15dce9cf8bcdd12b4437a5; original global index 7882.
def localCycle00110 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 667d5313ea3adfa43ff9941b980cd6e9f116ecf727e9f8388b696f870a52a51e; original global index 7968.
def localCycle00111 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 66b60b1820266d6a67d2cb762d086539a625f21846d5f247f46fd6aa192840c7; original global index 7984.
def localCycle00112 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 13 2, .gapLower 6 2, .gapUpper 4 3]

-- Original cycle 6759d2307de4ea5cb144ab7cd3c25b3ff471c7a5d961f9c7ee63685d8dd03e6c; original global index 8034.
def localCycle00113 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 695fa27a81ceeb5b114fc210e29eff9f6b6cc1cfebbd79883b6c38c8891226fe; original global index 8199.
def localCycle00114 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 4, .distance 2 3, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 3, .theta 3]
    constant := ![4, -1, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 11 1, .triangle 21 0, .gapLower 3 0]

-- Original cycle 698af1f02b84b8a00977e8b2db6cfa0a5d54747e3ac2869874f997c9fceba94f; original global index 8207.
def localCycle00115 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle 6995e3d3fa2ad070dbbc508f20ae558ebac305b47954487201a34a09436a609d; original global index 8211.
def localCycle00116 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 699a74c268434f8c63051593fad9f34fd469cd77f6a70586c617b0f2ccc7aced; original global index 8213.
def localCycle00117 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 0 6, .distance 3 6, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 11 1, .triangle 32 1, .triangle 23 0, .gapLower 4 0]

-- Original cycle 6a456ddef9ac63c52116d78bd1d4e7f02693448616077dd6835c27ad822cef1d; original global index 8275.
def localCycle00118 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 6acf333a60f4713d289279c176fde67c0e8cc3c850abdd8b6163dfc91cf7a451; original global index 8315.
def localCycle00119 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 4 6, .distance 1 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 23 2, .gapLower 6 1, .gapUpper 4 2]

-- Original cycle 6d5eae054964afa3ef0ce91732afa76666292e6825c312905bc59b1f7ab2c515; original global index 8503.
def localCycle00120 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 26 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 6f1a044d5e6e42cfd1237a06566515d29ed9f7b5fb8ebe16a7347cef230cae0a; original global index 8615.
def localCycle00121 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 11 2, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 70b4cbe3b213e03669517bf16089793c803f10eb575f30949c84f4e20f43a95a; original global index 8737.
def localCycle00122 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 8 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 713c8556789a3988d0e13a5489691f8b8e0881325d92edaf53a5035cb9e9323d; original global index 8783.
def localCycle00123 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 2 6, .distance 2 5]
    constant := ![2, -2, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 30 1]

-- Original cycle 736627489f95718cb3b618e6f1c50a22c35ee05c4297fe5f9e02bb735addf167; original global index 8941.
def localCycle00124 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 6, .distance 1 6, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .gapLower 6 2, .gapLower 6 1, .triangle 23 1, .gapLower 4 0]

-- Original cycle 7383c2fd04b9f89ba608df4b0feaa389e436469d596bfaae8ccda168d8ca8166; original global index 8954.
def localCycle00125 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 22 0, .gapLower 4 0]

-- Original cycle 7407f547a131912b3351e7094b3c72641d9be3de43611d18c0f4f8d16ee160f2; original global index 9002.
def localCycle00126 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 2 6, .distance 3 6, .distance 2 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 27 2, .gapLower 6 4, .gapUpper 3 4]

-- Original cycle 74428463e9621c620d208c988029fcf0560c63093a7f44577e0488efc498ef7e; original global index 9018.
def localCycle00127 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 4 5, .distance 0 4]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 4, .gapLower 5 3, .gapUpper 4 3]

-- Original cycle 7836faa15e8d3b927e932c45d90c7d365b869f7927516ea62ea4d6c16a92ca64; original global index 9291.
def localCycle00128 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 11 2, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 7840523d6c8826a91b10e3f48494c82100cbacbcdb2c7def3221cda4c0196d2c; original global index 9295.
def localCycle00129 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 22 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Original cycle 78b1fe1af8821c08d3a36b2d40cdd98f9c3e822d9d6b463b47de332be50f2661; original global index 9337.
def localCycle00130 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 11 2, .triangle 13 1, .triangle 23 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 7a7e06bce3fc454f3284a154ee9d473c6ce5fd5f5c4da0bcf69d3b833c510b10; original global index 9477.
def localCycle00131 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 0 5, .triangle 12 0, .triangle 22 2, .gapUpper 1 5]

-- Original cycle 7dba22666913058dfcd695f1b066a328ab0e1844366b1ee16c708fffc5639e71; original global index 9760.
def localCycle00132 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 10 0, .triangle 11 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 7e288f5d32c0a54ce241fa1715457a1638716314ce592bcab7958d66e0718e90; original global index 9801.
def localCycle00133 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 4 2, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle 7e521e749326aabfa04a27347c57f6ab85aeeeb8ef6b807143bb7377bd78d360; original global index 9811.
def localCycle00134 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 21 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 7fefbe8c2990c158f20e5412987fda80bd2eadc3caecba53edf7e78946ec4af3; original global index 9922.
def localCycle00135 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Original cycle 80fb0a2a24859ca520d57a74f9a245e2630b61c94093386a384d3fc4e421e1ea; original global index 10010.
def localCycle00136 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 82dd2fb80653f9f47f7b6c0f68bcf8458c633f8418bd1142b9a9edc572b5fe94; original global index 10149.
def localCycle00137 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 11 1, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 82fb94425248885b57ee5565454df0845f7cb955dd6578a1030aeae9db8fa797; original global index 10156.
def localCycle00138 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 21 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 830262eaaf5d9500735e39b656bd06480d5209bb74f0b6c0f61ac39376d078df; original global index 10158.
def localCycle00139 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![4, -1, 0, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 0, .triangle 5 2, .triangle 11 0, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 8319aeea723fea615e010f19dbfcbad90c233f5a94b0ed6b9e6ad1163acfc96a; original global index 10167.
def localCycle00140 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 4 0]

-- Original cycle 84433a8b176d416133cf6cf9d42f32191eb58c207f91e57b6fb67083b57bc58f; original global index 10271.
def localCycle00141 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 2 6, .distance 3 6, .distance 2 3]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 27 2, .gapLower 6 4, .gapUpper 3 4]

-- Original cycle 847a268c976e8df8fe03fb1f0c27a107008c3c35aa9f6715e4d619a2abe7d9b6; original global index 10287.
def localCycle00142 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, 3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 848ae7f983bfd2b84c683b16a51e36d1546711c23b08f166315be4ffd937ad71; original global index 10292.
def localCycle00143 : Cycle where
  length := 4
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .theta 6]
    constant := ![3, -2, 0, -2]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 18 2, .gapLower 6 0]

-- Original cycle 8524c5ef5f752180703ece070635db0d2a47d6f55161065084077d58a8150f28; original global index 10331.
def localCycle00144 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .gapLower 6 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 8562be67189006f106fd26a72bb352fb290872b745a093ebcbcf9e74d97448ba; original global index 10348.
def localCycle00145 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 0 6, .distance 0 2]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 2 2, .triangle 8 2, .gapLower 0 1]

-- Original cycle 8668ff70708c3b293c7263a66a5fc4575559d2e87290da42c34d5eb32d67cf69; original global index 10421.
def localCycle00146 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 20 0, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 8804d5ba5057521f6a3b6f5451c4f1746a8252094ecf642daee3c5090ce7d88c; original global index 10547.
def localCycle00147 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, -1, -3, 3, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3]

-- Original cycle 891b8045e15650dad8e1f58bb19278ed8edf7f9f67669445b312233449a46611; original global index 10611.
def localCycle00148 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -3, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 12 2, .gapLower 0 3, .triangle 11 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 8c316aa76d7b6ff22d15616bedd1f39f6965f0be5ff3225732052a4e9198b0e6; original global index 10849.
def localCycle00149 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 13 1, .triangle 23 2, .gapLower 6 0]

-- Original cycle 8c61b92ff77577d9a7282c68b81ff06b1b5c637b47eb996e9b1e6f59484dc554; original global index 10865.
def localCycle00150 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 0, .gapLower 1 3, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 8cf2ce5b1b7b5586af39cca2044ad67de702482118225e6441c3496236038e9c; original global index 10903.
def localCycle00151 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 0 3, .distance 3 6, .distance 4 6, .distance 1 6, .distance 1 4, .theta 4]
    constant := ![3, -1, 0, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 5 2, .triangle 11 0, .triangle 32 1, .gapLower 6 1, .triangle 23 1, .gapLower 4 0]

-- Original cycle 8e8e26f5231900cabb0a59829e30fe7c0ebea3d0563b1fc8d6609d7c4a14236b; original global index 11031.
def localCycle00152 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 8f21b97effd4452ebe7d3ab7bcb3f09bbb2315d176ef6671ce4d1aec1f6721ac; original global index 11074.
def localCycle00153 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 900171a7f628707d083590eee1825eaa89ede3596eda0dc5b79bc15a43f4c9de; original global index 11148.
def localCycle00154 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 0 6, .distance 3 6, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, -1, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 11 1, .triangle 32 1, .triangle 23 0, .gapLower 4 0]

-- Original cycle 9376e7eb9c8fbf4bf485914028b189138d39ee1d0b9911976e183f94e427ac99; original global index 11439.
def localCycle00155 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .distance 1 4, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 22 0, .gapLower 4 0]

-- Original cycle 93a791f11b3bc006e07b52f4658771507ba7f4ee41f5b268093eceddf3525bba; original global index 11454.
def localCycle00156 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 4, .distance 4 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 2, .triangle 13 0, .triangle 23 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 9402900322bbc6536aeac733f4f03495a888f641f3001ba5896cc3a315ab23c4; original global index 11479.
def localCycle00157 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 2 3]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 2 3, .gapUpper 5 5, .gapLower 6 5, .triangle 27 0]

-- Original cycle 94b772d32d71720540486c946813e24e54d0a9981dbb124e3fcd85755d914a7c; original global index 11541.
def localCycle00158 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 11 2, .gapLower 6 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 94c8a05f4f61c9551ed4b6f466223f48c3b66904e0ff85e6d5c5abfdf5e866cc; original global index 11548.
def localCycle00159 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 4 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 95ef3aaeb29308dc6538f754dd59019e7581a2ac53dc7fa92203b5e0c41bc4c8; original global index 11659.
def localCycle00160 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 2 2, .triangle 13 0, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle 9633d91b54b4066121da259195699b6a9bea99ab5ae532c19591e233b26f3430; original global index 11679.
def localCycle00161 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 11 2, .triangle 13 1, .triangle 23 0, .gapLower 4 0]

-- Original cycle 9699f8cce5fd1c4879891c891a2855a895686313e50398f1834ffda4b8688b33; original global index 11712.
def localCycle00162 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 11 2, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 96af2c4ba3b8b921a6277af989a29af2ddb1a73fcb584f3e3c5cb25f32f4a22c; original global index 11715.
def localCycle00163 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 4 6, .theta 6, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, -1, 0, -2, -2, 3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .gapLower 6 1, .gapLower 6 0, .corridorUpper 5 6, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 97463734e467ac8a40a0a07451f56933576f56f6c6d2e4a132cd4ca4fc0a06a0; original global index 11756.
def localCycle00164 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .gapLower 6 2, .triangle 21 1, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 97a20f675db9798d563da38335e1e934aa178b2888339d5f84041780390893e0; original global index 11778.
def localCycle00165 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![4, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 11 1, .triangle 21 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 97d79ff56b07af0a95d9f45c715011fcbe136efd70c26ad37a985634b3a5d8c1; original global index 11793.
def localCycle00166 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 9832437c09f00eb82a8a90b24df520663f4f1bb8ebc3ff9235e225f3c9587806; original global index 11824.
def localCycle00167 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 98eea8880094055b4bcbceecace3c8019f4bd65cd03f72a694483b4605b0f45f; original global index 11876.
def localCycle00168 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -2, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 12 2, .gapLower 0 3, .gapLower 0 2, .triangle 11 1, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 994c99f3b7736bed44fe8b09d554e92a01a031e7768c0761d7579ce08525a9ef; original global index 11902.
def localCycle00169 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 4 6]

-- Original cycle 9953a60e7d042ddde80d837709816e6ab65499cff7e028e038bfa2fe7922d95f; original global index 11904.
def localCycle00170 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 11 2, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 99f4d6b13c1c5c464270d5808d97f6b2fbc2bf7bc2dcdaff478ecef7b3e4c434; original global index 11953.
def localCycle00171 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 9a4812b79d44b7bcb6cbdec1a4bda1f22f8974bd3c8c2dd8786ec892dbe58f3b; original global index 11989.
def localCycle00172 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 9a90d67b2b597868cce2c70cc7a87c633ce900cbe9916ab1ba4484afed82dab0; original global index 12005.
def localCycle00173 : Cycle where
  length := 14
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .theta 0]
    constant := ![2, 0, -1, 0, -1, -1, 0, 3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 6, .triangle 2 2, .triangle 12 0, .triangle 22 2, .triangle 24 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0]

-- Original cycle 9ae95b0348c82b43a860217f3bfc6631801bfbacff122a7882aafb76ac2a859b; original global index 12038.
def localCycle00174 : Cycle where
  length := 5
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .theta 6]
    constant := ![3, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 0]

-- Original cycle 9be251bebf69eab9005c7632e0f84b6d2302b928e69f29c555556d526f4ecb56; original global index 12125.
def localCycle00175 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Original cycle a053f2d5b6c282a8ff8986d1179f96779d887c8c2b5a5a086d04810072e9a40f; original global index 12476.
def localCycle00176 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle a07627135ddc97c8910ac19eebca9c0a50d6b8f3d9574587180f82961317fae5; original global index 12486.
def localCycle00177 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 23 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle a1949d69b956962b5149dd5cd4d1596c22348752c0dec5c11de036ad3e68b1b3; original global index 12564.
def localCycle00178 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![4, -1, -1, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 9 0, .triangle 11 0, .gapLower 6 2, .triangle 23 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle a44981bccf878c8a259a6c0f66871d73585d2793ba20bbbe93f9a6174464db2b; original global index 12768.
def localCycle00179 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 2 5]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 30 1]

-- Original cycle a537e3acfed017ab7bac0fb914375f7fe756b7732152efca91045cba6551135d; original global index 12835.
def localCycle00180 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 12 0, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle a5417d781dc4f8f2905a8bf766bc3cb3ec4c3719da84ace7749b14c1626a6fdb; original global index 12838.
def localCycle00181 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 10 0, .triangle 11 0, .triangle 21 2, .triangle 23 1, .corridorLower 4 6]

-- Original cycle a571e62a5d5c8cfc2b9eced04425ca3b34f27adaded25a181d0f75c7d2cd8156; original global index 12855.
def localCycle00182 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 3, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 26 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 25 0]

-- Original cycle a6411c980e8c472b8cc78c9efe7e7131e83aedba23a40375c6c4ee47077085cb; original global index 12915.
def localCycle00183 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .gapLower 2 4, .gapLower 3 3, .triangle 11 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle a811e52c743462052c0d849f77d7e9a9264272dd93017707ded69d395923be6b; original global index 13089.
def localCycle00184 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 23 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle ab5edae51715eef66bc707ac92790f8bedc2b06ea10a2b2b29cd1f1fc6be498a; original global index 13353.
def localCycle00185 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Original cycle ab9866f988c244c56496c9ec3b2b8eaa1e0815ebc12a1fea1f1b81399ca38318; original global index 13365.
def localCycle00186 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, 3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle acfc40650e96ff3a0c83b0058671669e7dc0e74775d33b1d20c3e6484f9cd515; original global index 13483.
def localCycle00187 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 6 2, .triangle 9 1, .triangle 10 0, .triangle 20 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle ae53ab2bf76c88ab30d0506d32c714bf9d2c30e91cf83414aae151801618e307; original global index 13606.
def localCycle00188 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -2, -2, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .gapLower 0 4, .gapLower 0 3, .triangle 11 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle ae80940495f6708f80a02bd711b4daf62d2536fad54af12d094af2bec9e0b6de; original global index 13620.
def localCycle00189 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 13 1, .triangle 23 0, .gapLower 4 0]

-- Original cycle af5291d7735d5d5df8a4c9022363a9fef801f54f4665066a62cb5117dc18026d; original global index 13696.
def localCycle00190 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -1, 0, -3, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true] }
  origin := ![.triangle 2 2, .triangle 9 1, .triangle 11 0, .triangle 32 1, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle af7148932a4a810a08f7c1c33caa6b7902ba2e8943f3a28c5fe096d272a24c93; original global index 13703.
def localCycle00191 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle b0b87c15af648e8ca3b7bd3449be6c8beb1224c1abaa1bc67128d07a71544743; original global index 13799.
def localCycle00192 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 6, .distance 1 6, .theta 1]
    constant := ![3, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 2, .gapLower 6 2, .corridorLower 1 6]

-- Original cycle b1ac70f9df9970f6129cf3f0c66cc288c2d41ce0553ce209d24fc928d629d25a; original global index 13883.
def localCycle00193 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 13 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle b1c15f3439a988ca1451874963f39d17d49c2a85d940a3c948b2363e9b666ac9; original global index 13891.
def localCycle00194 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle b274d4f9ec34ec7d1d31b27e7fa49066a614daf181435c412510c140d398efd3; original global index 13944.
def localCycle00195 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 3, .triangle 11 1, .triangle 10 0, .triangle 20 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle b2972c62279d79000da1604ea9e3bfd9f4272af61190db52cacd52cde6c3c341; original global index 13960.
def localCycle00196 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, -2, 0, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 8 2, .triangle 13 1, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle b4d02be5d159972a44faa22c85c41661c3064cf5469bcddaafecbfe76b563d60; original global index 14118.
def localCycle00197 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 19 1, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Original cycle b64243a76e2fbd174532b6c936aa635bf3b3560c60dea5eaba257d9e94a83b27; original global index 14241.
def localCycle00198 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 23 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle b83660a8e74079779894cf6d5be791f827505f160f8dec18f2365426692a8745; original global index 14372.
def localCycle00199 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 4 1, .triangle 21 1, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle b95ecb5e3d9f7c923e8f0a988d664dacfc79fdc5e110f0e54252acd2c03bce79; original global index 14464.
def localCycle00200 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 2 6, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 30 1]

-- Original cycle ba37aaa228d27d06a90e34c73f7158193d91b66cab66a6e0cea768f669cbb9f0; original global index 14539.
def localCycle00201 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle be353b236025491ee7377d46688b69f8910716086190297316e4be477f32e8bf; original global index 14835.
def localCycle00202 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .triangle 11 1, .triangle 10 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle be41a167481ab2baf0c7b288edbcfb7b5205cbd94b89897d09d3689d30cf87ee; original global index 14839.
def localCycle00203 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 8 2, .triangle 11 1, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle be87640619f0df6aa88bca7a1b9f1a280a75eca60ea4ac1efa58f3d58b0fa5c1; original global index 14866.
def localCycle00204 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 4 5, .distance 1 4, .theta 4]
    constant := ![3, 0, -2, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 11 1, .triangle 10 0, .triangle 31 1, .triangle 22 0, .gapLower 4 0]

-- Original cycle beb913d5c7d78c67c973a93e9689e55d98f97e100558ed66c10738f89cbaa47d; original global index 14881.
def localCycle00205 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 4 6]

-- Original cycle bf3610120027419aaa939f5748db4af9fed91594bb18d3d9e327a58b4dbfb32f; original global index 14925.
def localCycle00206 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 2 1, .triangle 19 1, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle c142898dfc6f47d74233c96055563e8002d56320b4b67eec3094f0b37b3c6ffa; original global index 15086.
def localCycle00207 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 4 5, .distance 0 4]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 4, .triangle 12 1, .gapUpper 4 3]

-- Original cycle c3025788d8793cd4da0d3fbe8d0b0268609f2449b7c020800c566da8dfc2591c; original global index 15220.
def localCycle00208 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -3, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 11 1, .triangle 10 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c3695c62f2596950b80605865d62ac78904ccbfa9bef2ff9be48c96b3b97aa68; original global index 15250.
def localCycle00209 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .theta 6, .distance 5 6, .distance 3 6, .distance 2 3, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, -1, -1, -2, 2, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .gapLower 6 0, .gapLower 6 6, .triangle 33 2, .triangle 27 0, .triangle 5 2, .triangle 10 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle c3714e283e21533cbdf416e3ed653e9d5e1c387bfaba344be5cfc3dfbac2cb03; original global index 15252.
def localCycle00210 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .gapLower 2 4, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle c596f5695ec899aba4c5fd2ad40582ce3c600eb3aff3faf7508d04b53c8ef24a; original global index 15412.
def localCycle00211 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c73f8d3196269f6e49dfbca1d00fc41cc4e106b8afa56e6b8851b5b4ff11f8c1; original global index 15549.
def localCycle00212 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle c7740125cd20bc72a781266dd17ca40b0d3f5f7d7ec6dd597fe35fb3b6d7c9dd; original global index 15566.
def localCycle00213 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle c77feddf6b8c573e81f43adb4e6265193cfb5ec564e554b468f6efbd73a9fe8c; original global index 15569.
def localCycle00214 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle c8fe1ebf1571d4ac74030ce5648670c4adb6577d796d736229ff2001384a75fa; original global index 15697.
def localCycle00215 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .gapLower 6 3, .triangle 13 1, .triangle 23 0, .gapLower 4 0]

-- Original cycle cb2382c28815e41617617d758e35ea7dd462b45b1133bfbf6bc82c5001eaaac8; original global index 15869.
def localCycle00216 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 8 2, .gapLower 6 3, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle cda6c428ddacb5c815b689eab66e7cc5c7a15581a756c543edeebecd2ef182f1; original global index 16073.
def localCycle00217 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .triangle 13 1, .triangle 23 2, .gapLower 6 0]

-- Original cycle d0707f29f5699c38e5f68713c6673050ff6e179b156f69901eb4641388c039d6; original global index 16270.
def localCycle00218 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle d09dc4b38200820825f12d7fa773d660c7a50abe946ce64b53560d467f3d493e; original global index 16281.
def localCycle00219 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 5 2, .triangle 11 0, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle d158b39bde4b5a30be7918012ca0cc842ba5fd4faf99b8956f651ab3a51c006b; original global index 16342.
def localCycle00220 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle d255bc8bf1581b7c822e6949a8ae0a045b93d43576331a4b238c6ffabe4caca8; original global index 16411.
def localCycle00221 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 5 2, .triangle 11 0, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .gapLower 4 0]

-- Original cycle d33575043a1a6632f0e586dcd35f8045d53f79109fc919f6727389f39afc6743; original global index 16476.
def localCycle00222 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 11 1, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle d371c5a29319d0acae9f8dac81a79a13076b037710450a6d7af8b0be1e361100; original global index 16494.
def localCycle00223 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .gapLower 0 2, .triangle 8 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle d527663cb918b7e5a196a248abc610afe1f0b5dfc77b449991dfce96f3ab848b; original global index 16632.
def localCycle00224 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .gapLower 6 3, .triangle 13 1, .triangle 23 0, .gapLower 4 0]

-- Original cycle d53b4072e6c837fb93dfaa949638a9cb1550ecffb5f7ebb00d900d4820c086c8; original global index 16641.
def localCycle00225 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .gapLower 6 3, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle d5b33e7e2d4c5dfb7617c390611572269a2390c4a03bd638c83b48527bb9f6fc; original global index 16681.
def localCycle00226 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 6, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 11 2, .triangle 13 1, .gapLower 6 1, .triangle 23 1, .gapLower 4 0]

-- Original cycle d8124fb7b9e488c41265cfb01d2fe6511b9eb7951904d3123ab31c63c9cbc7c5; original global index 16863.
def localCycle00227 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![4, -1, -1, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 25 0, .triangle 27 0, .gapLower 6 3, .triangle 23 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle d9072c930f8cdeeb972532536a1057d703d388ba44bd5bb329d705b88d454015; original global index 16951.
def localCycle00228 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 6, .distance 3 6, .distance 0 3]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 2, .triangle 11 1, .gapUpper 3 2]

-- Original cycle d9dc746ff98be47ce2e4336eb84fa1e14a654441d8dcde70ed7112638bf9ee36; original global index 17020.
def localCycle00229 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 8 2, .gapLower 6 3, .triangle 21 2, .triangle 23 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle da2d3e0ca4a2e526bc8521e9b469608a2e37aa1b980f349d54af1cdb4462abdc; original global index 17047.
def localCycle00230 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, -1, -1, -1, -1, 0, 3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 22 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle dc5d83bc71ccbeb02fde115a62ec6cc8b70604b73354f407353c7777d6b6f05b; original global index 17222.
def localCycle00231 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -2, 0, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .gapLower 0 4, .triangle 10 1, .gapLower 0 2, .triangle 11 1, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle de971f97a2f2f3a033ef2cf623be98265dc315eb998793858da3bf96929e4088; original global index 17407.
def localCycle00232 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 2 6, .distance 4 6, .distance 2 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 29 2, .gapLower 6 3, .gapUpper 4 4]

-- Original cycle dfa59f3f2e0e5849061fdeeb14e6b1c8b6eb423298711390d01ff1215bc97460; original global index 17471.
def localCycle00233 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle e06384b1b9d7b0011ce01ac5b5743eb626e62cebea6b338bf799a89b28b52f74; original global index 17541.
def localCycle00234 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle e13c6b55ab53b37b858f5ff328d2fef5be5f99ff7a28a620237ac8d5fddf06a7; original global index 17614.
def localCycle00235 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![4, -1, -1, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 25 0, .triangle 27 0, .gapLower 6 3, .triangle 13 1, .triangle 23 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle e17bc05b7d4256acd0bc27724a6d7c0aa045bd81aaf0d826f70af30cec8140d0; original global index 17633.
def localCycle00236 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle e1982abb9cd9e6ec7ec6eb46bb11ec98bc13cdd8dbbc46dde20df17360a7390b; original global index 17640.
def localCycle00237 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Original cycle e2c2dc82005be310c7666793eb02945af3efda547b7e95110dd6c40afa29d91d; original global index 17734.
def localCycle00238 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 2 3]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 2 3, .gapUpper 5 5, .gapLower 6 5, .triangle 27 0]

-- Original cycle e31d784de76b8579027ace212e03f552a8b7e9112568bf3a725f3dce71c494a5; original global index 17760.
def localCycle00239 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle e3222235f0f988abdaa1432edd561bcd39a7641bf74a99ad9c6de578047d7faf; original global index 17764.
def localCycle00240 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 2 6, .distance 4 6, .distance 2 4]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 29 2, .gapLower 6 3, .gapUpper 4 4]

-- Original cycle e32d008b72a6f9cd43a2a393f24a99ea83fbfa90976d902015ed7c573887e132; original global index 17770.
def localCycle00241 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 24 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle e36844ac09df1c214845ec8dd39aa44962ca4e1e8dcd7476eb2acaf27447eca0; original global index 17783.
def localCycle00242 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Original cycle e3716406cb9247eb1d9cbcfb4ff7ca7e807b8813de501b426b927ee9feb57fdd; original global index 17788.
def localCycle00243 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .gapLower 6 3, .corridorLower 4 6]

-- Original cycle e3931cc5002d7a6fb50d0c335efb7f21d67fb2142c88ba7115ea193531921f5e; original global index 17796.
def localCycle00244 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 31 1, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle e56c55a94f9dd2e907ac0c0623493597cd84f30c7d42df076f61f71a9dc733fc; original global index 17939.
def localCycle00245 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -1, 0, -2, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true] }
  origin := ![.triangle 2 2, .triangle 9 1, .triangle 11 0, .triangle 32 1, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle e5ac8546e097864b1ffc71cb151e31dafb7a224f264fc4e2c3c48f1d08005af4; original global index 17969.
def localCycle00246 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle e5f9bc627c20203ba4bc4babe15c756ace3003c32f6b86e9d4e7cb03470a6c3a; original global index 17995.
def localCycle00247 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle e8105de9b61faab931befd8c2d34411d9d62b3706521e6ceed4bb44cb1d1e4ab; original global index 18148.
def localCycle00248 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle e8f85b1db4e0bf4ccec2891eb6f0e55a72c4ee33a5013697bee15214319a9d1b; original global index 18206.
def localCycle00249 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Original cycle e9266149818abe3de1024157f08e187103953a467aa6af0a68f342e30c81044f; original global index 18219.
def localCycle00250 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 14 2, .gapLower 6 2, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0, .thetaLower 0]

-- Original cycle eb2381287ee5c7bc5d867816ba99141ddcf62f2000c09d2fefde74c33054eac6; original global index 18359.
def localCycle00251 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 11 2, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle ed60fcbfaac456c272fda3840a339aa491b5be200325b05e92a4dd745f3a11ee; original global index 18531.
def localCycle00252 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .theta 6, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, -1, -1, -3, 3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle ed90b425040fe28c340ff3afc3d1d482be193ee593b5df1d727ae249a749cfef; original global index 18547.
def localCycle00253 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle efb8122bc47be683933902db43b66e38972da27c45a6e04e02d53879fcae6f0a; original global index 18699.
def localCycle00254 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle f15e7a77c25271ba76100e56a740f4d286141d2b292e65372707faf40f312982; original global index 18818.
def localCycle00255 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 6, .distance 3 6, .distance 0 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 11 2, .gapLower 6 3, .gapUpper 3 3]

-- Original cycle f2e56f5e1c43f74eb3fc457ca5984bb28968d4dd4efed4429a3205b7f138f796; original global index 18932.
def localCycle00256 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 6, .distance 1 6, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .gapLower 6 2, .triangle 4 1, .triangle 23 1, .gapLower 4 0]

-- Original cycle f377ac7383f5b37d8e41780efe76fb18098d381cc4aa1edb9d16e6f44b922990; original global index 18992.
def localCycle00257 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .theta 0]
    constant := ![2, 0, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true] }
  origin := ![.gapLower 0 6, .triangle 2 2, .gapLower 0 4, .triangle 10 1, .triangle 11 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0]

-- Original cycle f388667a8e664bd14862a583b265151edb16fa38851cd46a8492977fbe5d4cea; original global index 19003.
def localCycle00258 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 8 2, .gapLower 6 3, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle f3abc699a30265fa8783dc12190688ccbe8d1a1519e0f390b255c3a2de02859d; original global index 19008.
def localCycle00259 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -3, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 2 2, .triangle 13 0, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle f3b6152cc5b2472e1a49fafaabd5bb0d3483d470f4066ce261efdfd94722a328; original global index 19011.
def localCycle00260 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 4, .distance 0 5, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .theta 0]
    constant := ![2, 0, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.gapLower 0 6, .triangle 2 2, .triangle 12 2, .gapLower 0 3, .gapLower 3 2, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0]

-- Original cycle f3e01d538303660bb62b1bd57d29197d6af7c14d1354aa7716c4ca49ef6163d2; original global index 19021.
def localCycle00261 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 0 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 11 1, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle f72c00c826617c8ac156a798dbbc68dede43b285eba830807ee0c9c64d8eef86; original global index 19275.
def localCycle00262 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 3, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle f7c17a28af6a1691ef40f445f77931ce61da3333a60d648b2d9ed1dc37864627; original global index 19315.
def localCycle00263 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle f83774d6d7e900d5f9153076c8e574a41100da0c2fe12f62b6ae7cdadf8dffc8; original global index 19359.
def localCycle00264 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle f96da5d9de2f5c1487acfc9d0ff654573e8b9be8c7f219858fe2d27c8d739a26; original global index 19446.
def localCycle00265 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .gapLower 6 3, .corridorLower 4 6]

-- Original cycle fa938fcce718e8f86e65f2fb273e2f22d63ff56054d463e8d5f3e77795265892; original global index 19547.
def localCycle00266 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -3, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 11 1, .triangle 10 0, .triangle 20 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle fab1d20a293f25109b00212fa5be4985952329adbdea022e109da24adb2dcfae; original global index 19559.
def localCycle00267 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 4 0]

-- Original cycle fae187be62870b96a6b8944492a6c34e0cd0753691921fd73ed46e7257750683; original global index 19578.
def localCycle00268 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .triangle 8 2, .gapLower 6 2, .triangle 23 2, .gapLower 6 0]

-- Original cycle fb81a2415727b3bd7148901fc65015d194a1667abe3cf5b149dfdc2339691c46; original global index 19636.
def localCycle00269 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle fc13bfc353811fb20032440ce9ee8a3f45b2e28a193a8ecd06893890e5b300ea; original global index 19682.
def localCycle00270 : Cycle where
  length := 4
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .theta 5, .zero]
    constant := ![0, 1, -2, 0]
    coefficient := ![1, 1, -1, 0]
    strict := ![false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapUpper 5 6, .thetaLower 5]

-- Original cycle fd2f013c30b797f7f489f6a0a4e267739f357201d88d58a6dd3a3035eb14336c; original global index 19788.
def localCycle00271 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 6, .distance 3 6, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, -1, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .gapLower 0 2, .triangle 11 1, .triangle 32 1, .triangle 23 0, .gapLower 4 0]

-- Original cycle fdfa40572bc87005d0870fc457c646f14bb3f0d4466b2d63e39e8887386bf262; original global index 19847.
def localCycle00272 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, -1, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 11 2, .triangle 13 1, .triangle 23 0, .gapLower 4 0]

-- Original cycle fed3be973c18c285504e8239364f02e95e24f36253163a598bd92153f52a5aec; original global index 19924.
def localCycle00273 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3]
    constant := ![-1, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.triangle 11 0, .gapLower 6 2, .gapUpper 4 3, .triangle 9 1]

-- Original cycle ff12ef4aaa0981941f5a0f8f9f65d84da09633eb4313270e317d8db93a058936; original global index 19940.
def localCycle00274 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, 0, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 2, .triangle 21 1, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle ff1693fa352988706e534d05507c06ca3f26372cad25c2043efbf58ff5d911fc; original global index 19945.
def localCycle00275 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .theta 6, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, -1, -1, -3, 3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle ff72d0e06c7d596387f98b8967dcd96a17d845cfd357e27f40cd51a4a11f51a2; original global index 19972.
def localCycle00276 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .theta 6, .zero]
    constant := ![0, 3, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 1, .corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .gapLower 6 0, .thetaLower 6]

-- Original cycle ffb9e4e2f64a78843670dca930a9a9baafc45ebde1cfbb91f46e4be21fc38923; original global index 20001.
def localCycle00277 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 5, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 2 2, .gapLower 0 4, .gapLower 5 3, .triangle 22 2, .gapUpper 1 5]

def library : Library := fun id => if id < 139 then (if id < 69 then (if id < 34 then (if id < 17 then (if id < 8 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none)))) else (if id < 12 then (if id < 10 then (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none)) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))) else (if id < 14 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)))))) else (if id < 25 then (if id < 21 then (if id < 19 then (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))) else (if id < 29 then (if id < 27 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none))) else (if id < 31 then (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none))))))) else (if id < 51 then (if id < 42 then (if id < 38 then (if id < 36 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none))) else (if id < 40 then (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none)) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none)))) else (if id < 46 then (if id < 44 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none)) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))) else (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none)))))) else (if id < 60 then (if id < 55 then (if id < 53 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none))) else (if id < 57 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))))) else (if id < 64 then (if id < 62 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none)) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))) else (if id < 66 then (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)))))))) else (if id < 104 then (if id < 86 then (if id < 77 then (if id < 73 then (if id < 71 then (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none))) else (if id < 75 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)))) else (if id < 81 then (if id < 79 then (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none)) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none))) else (if id < 83 then (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none)) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)))))) else (if id < 95 then (if id < 90 then (if id < 88 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none))) else (if id < 92 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none))))) else (if id < 99 then (if id < 97 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none))) else (if id < 101 then (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none))))))) else (if id < 121 then (if id < 112 then (if id < 108 then (if id < 106 then (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none))) else (if id < 110 then (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none)) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none)))) else (if id < 116 then (if id < 114 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none))) else (if id < 118 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none)) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none)))))) else (if id < 130 then (if id < 125 then (if id < 123 then (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none)) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none))) else (if id < 127 then (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none)) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none))))) else (if id < 134 then (if id < 132 then (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none)) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none))) else (if id < 136 then (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none)) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none))))))))) else (if id < 208 then (if id < 173 then (if id < 156 then (if id < 147 then (if id < 143 then (if id < 141 then (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none)) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none))) else (if id < 145 then (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none)) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none)))) else (if id < 151 then (if id < 149 then (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none)) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none))) else (if id < 153 then (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none)) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none)))))) else (if id < 164 then (if id < 160 then (if id < 158 then (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none)) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none))) else (if id < 162 then (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none)) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none)))) else (if id < 168 then (if id < 166 then (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none)) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none))) else (if id < 170 then (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none)) else (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none))))))) else (if id < 190 then (if id < 181 then (if id < 177 then (if id < 175 then (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none)) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none))) else (if id < 179 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id = 178 then some localCycle00178 else none)) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none)))) else (if id < 185 then (if id < 183 then (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none)) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none))) else (if id < 187 then (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none)))))) else (if id < 199 then (if id < 194 then (if id < 192 then (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id = 191 then some localCycle00191 else none)) else (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id = 193 then some localCycle00193 else none))) else (if id < 196 then (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none)) else (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id = 198 then some localCycle00198 else none))))) else (if id < 203 then (if id < 201 then (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id = 200 then some localCycle00200 else none)) else (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none))) else (if id < 205 then (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id = 204 then some localCycle00204 else none)) else (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none)))))))) else (if id < 243 then (if id < 225 then (if id < 216 then (if id < 212 then (if id < 210 then (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none)) else (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id = 211 then some localCycle00211 else none))) else (if id < 214 then (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id = 213 then some localCycle00213 else none)) else (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none)))) else (if id < 220 then (if id < 218 then (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id = 217 then some localCycle00217 else none)) else (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id = 219 then some localCycle00219 else none))) else (if id < 222 then (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id = 221 then some localCycle00221 else none)) else (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id = 224 then some localCycle00224 else none)))))) else (if id < 234 then (if id < 229 then (if id < 227 then (if id < 226 then (if id = 225 then some localCycle00225 else none) else (if id = 226 then some localCycle00226 else none)) else (if id < 228 then (if id = 227 then some localCycle00227 else none) else (if id = 228 then some localCycle00228 else none))) else (if id < 231 then (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id = 230 then some localCycle00230 else none)) else (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id < 233 then (if id = 232 then some localCycle00232 else none) else (if id = 233 then some localCycle00233 else none))))) else (if id < 238 then (if id < 236 then (if id < 235 then (if id = 234 then some localCycle00234 else none) else (if id = 235 then some localCycle00235 else none)) else (if id < 237 then (if id = 236 then some localCycle00236 else none) else (if id = 237 then some localCycle00237 else none))) else (if id < 240 then (if id < 239 then (if id = 238 then some localCycle00238 else none) else (if id = 239 then some localCycle00239 else none)) else (if id < 241 then (if id = 240 then some localCycle00240 else none) else (if id < 242 then (if id = 241 then some localCycle00241 else none) else (if id = 242 then some localCycle00242 else none))))))) else (if id < 260 then (if id < 251 then (if id < 247 then (if id < 245 then (if id < 244 then (if id = 243 then some localCycle00243 else none) else (if id = 244 then some localCycle00244 else none)) else (if id < 246 then (if id = 245 then some localCycle00245 else none) else (if id = 246 then some localCycle00246 else none))) else (if id < 249 then (if id < 248 then (if id = 247 then some localCycle00247 else none) else (if id = 248 then some localCycle00248 else none)) else (if id < 250 then (if id = 249 then some localCycle00249 else none) else (if id = 250 then some localCycle00250 else none)))) else (if id < 255 then (if id < 253 then (if id < 252 then (if id = 251 then some localCycle00251 else none) else (if id = 252 then some localCycle00252 else none)) else (if id < 254 then (if id = 253 then some localCycle00253 else none) else (if id = 254 then some localCycle00254 else none))) else (if id < 257 then (if id < 256 then (if id = 255 then some localCycle00255 else none) else (if id = 256 then some localCycle00256 else none)) else (if id < 258 then (if id = 257 then some localCycle00257 else none) else (if id < 259 then (if id = 258 then some localCycle00258 else none) else (if id = 259 then some localCycle00259 else none)))))) else (if id < 269 then (if id < 264 then (if id < 262 then (if id < 261 then (if id = 260 then some localCycle00260 else none) else (if id = 261 then some localCycle00261 else none)) else (if id < 263 then (if id = 262 then some localCycle00262 else none) else (if id = 263 then some localCycle00263 else none))) else (if id < 266 then (if id < 265 then (if id = 264 then some localCycle00264 else none) else (if id = 265 then some localCycle00265 else none)) else (if id < 267 then (if id = 266 then some localCycle00266 else none) else (if id < 268 then (if id = 267 then some localCycle00267 else none) else (if id = 268 then some localCycle00268 else none))))) else (if id < 273 then (if id < 271 then (if id < 270 then (if id = 269 then some localCycle00269 else none) else (if id = 270 then some localCycle00270 else none)) else (if id < 272 then (if id = 271 then some localCycle00271 else none) else (if id = 272 then some localCycle00272 else none))) else (if id < 275 then (if id < 274 then (if id = 273 then some localCycle00273 else none) else (if id = 274 then some localCycle00274 else none)) else (if id < 276 then (if id = 275 then some localCycle00275 else none) else (if id < 277 then (if id = 276 then some localCycle00276 else none) else (if id = 277 then some localCycle00277 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 3, 5, 4], ![1, 6, 0, 2, 5, 4], ![1, 6, 0, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 1, 4, 3, 0, 2]], proof := .tail 85 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17920)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 3, 5, 4], ![1, 6, 0, 2, 5, 4], ![1, 6, 5, 0, 2, 3], ![6, 1, 4, 0, 2, 3], ![5, 1, 4, 3, 0, 2]], proof := .low0 (![122, 145, 228, 148, 127, 74, 52, 7, 223, 60, 207, 131, 173, 271, 4, 277, 131, 3, 168, 231, 131, 25, 188, 131, 260, 54, 257, 30]) }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17921)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 3, 5, 4], ![1, 6, 0, 2, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 0, 2, 3], ![4, 1, 5, 3, 0, 2]], proof := .tail 37 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17922)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 3, 4, 5], ![1, 6, 0, 2, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 3, 0, 2]], proof := .tail 184 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17923)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 3, 4, 5], ![1, 6, 0, 2, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 1, 3, 0, 2]], proof := .tail 183 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17924)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 3, 5, 4], ![1, 6, 0, 2, 5, 4], ![6, 1, 0, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 4, 1, 3, 0, 2]], proof := .tail 32 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17925)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 3, 5, 4], ![1, 6, 0, 2, 5, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 0, 2, 3], ![5, 4, 1, 3, 0, 2]], proof := .tail 87 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17926)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 6, 3, 5, 4], ![1, 6, 0, 2, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 1, 3, 0, 2]], proof := .tail 241 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17927)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 6, 3, 5, 4], ![1, 6, 0, 2, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 1, 3, 0, 2]], proof := .tail 230 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17928)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 6, 3, 4, 5, 0], ![1, 0, 6, 3, 4, 5], ![6, 1, 0, 2, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 111 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17929)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 6, 3, 4, 5, 0], ![1, 0, 6, 3, 4, 5], ![6, 1, 0, 2, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 4, 3, 1, 0, 2]], proof := .tail 56 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17930)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 6, 3, 4, 5, 0], ![1, 0, 6, 3, 5, 4], ![6, 1, 0, 2, 5, 4], ![6, 1, 0, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 4, 3, 1, 0, 2]], proof := .tail 101 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17931)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 6, 3, 4, 5, 0], ![1, 0, 6, 3, 5, 4], ![6, 1, 0, 2, 5, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 0, 2, 3], ![5, 4, 3, 1, 0, 2]], proof := .tail 87 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17932)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 6, 3, 5, 4, 0], ![1, 0, 6, 3, 5, 4], ![6, 1, 0, 2, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 3, 1, 0, 2]], proof := .tail 37 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17933)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 6, 3, 5, 4, 0], ![1, 0, 6, 3, 5, 4], ![6, 1, 0, 2, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 3, 1, 0, 2]], proof := .tail 129 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17934)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 3, 4, 6], ![1, 0, 5, 2, 4, 6], ![1, 0, 5, 2, 3, 6], ![1, 0, 4, 3, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 27 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17935)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 3, 4, 6], ![1, 0, 5, 2, 6, 4], ![1, 0, 5, 2, 6, 3], ![1, 0, 4, 3, 2, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 210 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17936)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 3, 6, 4], ![1, 0, 5, 2, 6, 4], ![1, 0, 5, 6, 2, 3], ![1, 0, 4, 3, 2, 6], ![1, 0, 4, 2, 3, 5]], proof := .low6 (![147, 133, 104, 232, 64, 157, 239, 50, 144, 28, 174, 238, 34, 105, 240, 77, 238, 34, 159, 39, 238, 34, 169, 238, 262, 179, 44, 238]) }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17937)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 3, 4], ![1, 0, 5, 6, 2, 4], ![1, 0, 5, 6, 2, 3], ![1, 0, 4, 3, 2, 6], ![1, 0, 4, 3, 2, 5]], proof := .low6 (![95, 133, 253, 265, 126, 200, 20, 193, 256, 227, 141, 143, 116, 124, 227, 141, 123, 91, 227, 9, 263, 263, 205, 243, 243, 16, 36, 218]) }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17938)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 5, 6, 2, 4], ![1, 0, 5, 6, 2, 3], ![1, 0, 4, 3, 6, 2], ![1, 0, 4, 3, 5, 2]], proof := .tail 176 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17939)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 2, 4], ![1, 0, 5, 6, 2, 3], ![1, 0, 4, 6, 3, 2], ![1, 0, 4, 5, 3, 2]], proof := .tail 59 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17940)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 2, 4], ![1, 0, 6, 5, 2, 3], ![1, 0, 6, 4, 3, 2], ![1, 0, 5, 4, 3, 2]], proof := .tail 76 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17941)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 2, 4], ![1, 0, 6, 5, 2, 3], ![1, 6, 0, 4, 3, 2], ![1, 5, 0, 4, 3, 2]], proof := .tail 76 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17942)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 2, 4], ![1, 0, 6, 5, 2, 3], ![6, 1, 0, 4, 3, 2], ![5, 1, 0, 4, 3, 2]], proof := .tail 55 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17943)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 2, 4], ![1, 6, 0, 5, 2, 3], ![1, 6, 0, 4, 3, 2], ![1, 5, 4, 0, 3, 2]], proof := .tail 19 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17944)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 2, 4], ![1, 6, 0, 5, 2, 3], ![6, 1, 0, 4, 3, 2], ![5, 1, 4, 0, 3, 2]], proof := .tail 19 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17945)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 2, 4], ![6, 1, 0, 5, 2, 3], ![6, 1, 0, 4, 3, 2], ![5, 4, 1, 0, 3, 2]], proof := .tail 175 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17946)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 6, 0, 5, 2, 4], ![1, 6, 0, 5, 2, 3], ![1, 6, 0, 4, 3, 2], ![1, 5, 4, 3, 0, 2]], proof := .tail 19 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17947)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 3, 4], ![1, 6, 0, 5, 2, 4], ![1, 6, 0, 5, 2, 3], ![6, 1, 0, 4, 3, 2], ![5, 1, 4, 3, 0, 2]], proof := .tail 19 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17948)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 5, 3, 4], ![1, 6, 0, 5, 2, 4], ![6, 1, 0, 5, 2, 3], ![6, 1, 0, 4, 3, 2], ![5, 4, 1, 3, 0, 2]], proof := .tail 97 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17949)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 6, 3, 4, 5, 0], ![1, 0, 6, 5, 3, 4], ![6, 1, 0, 5, 2, 4], ![6, 1, 0, 5, 2, 3], ![6, 1, 0, 4, 3, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 175 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17950)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 3, 4, 6], ![1, 0, 5, 2, 4, 6], ![1, 5, 0, 2, 3, 6], ![1, 4, 0, 3, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 40 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17951)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 3, 4, 6], ![1, 0, 5, 2, 6, 4], ![1, 5, 0, 2, 6, 3], ![1, 4, 0, 3, 2, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 103 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17952)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 3, 6, 4], ![1, 0, 5, 2, 6, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 0, 3, 2, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 180 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17953)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 3, 6, 4], ![1, 0, 5, 2, 6, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 0, 3, 2, 6], ![1, 4, 0, 2, 3, 5]], proof := .low6 (![156, 259, 112, 189, 64, 157, 75, 160, 268, 149, 217, 238, 108, 98, 160, 160, 238, 160, 6, 51, 238, 250, 89, 238, 69, 179, 96, 238]) }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17954)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 3, 4], ![1, 0, 5, 6, 2, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 0, 3, 2, 6], ![1, 0, 4, 3, 2, 5]], proof := .tail 80 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17955)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 5, 6, 2, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 0, 3, 6, 2], ![1, 0, 4, 3, 5, 2]], proof := .tail 140 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17956)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 2, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 0, 6, 3, 2], ![1, 0, 4, 5, 3, 2]], proof := .tail 267 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17957)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 3, 4], ![1, 0, 5, 6, 2, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 0, 3, 2, 6], ![1, 4, 0, 3, 2, 5]], proof := .low6 (![78, 259, 251, 215, 272, 200, 246, 226, 47, 235, 141, 116, 130, 15, 235, 160, 160, 160, 48, 162, 128, 128, 100, 224, 224, 24, 161, 196]) }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17958)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 5, 6, 2, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 0, 3, 6, 2], ![1, 4, 0, 3, 5, 2]], proof := .tail 140 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17959)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 2, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 0, 6, 3, 2], ![1, 4, 0, 5, 3, 2]], proof := .tail 59 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17960)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 2, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 6, 0, 3, 2], ![1, 4, 5, 0, 3, 2]], proof := .tail 59 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17961)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 2, 4], ![1, 6, 5, 0, 2, 3], ![1, 6, 4, 0, 3, 2], ![1, 5, 4, 0, 3, 2]], proof := .tail 76 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17962)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 2, 4], ![1, 6, 5, 0, 2, 3], ![6, 1, 4, 0, 3, 2], ![5, 1, 4, 0, 3, 2]], proof := .tail 55 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17963)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 2, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 0, 3, 2], ![5, 4, 1, 0, 3, 2]], proof := .tail 1 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17964)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 6, 0, 5, 2, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 6, 0, 3, 2], ![1, 4, 5, 3, 0, 2]], proof := .tail 68 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17965)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 6, 0, 5, 2, 4], ![1, 6, 5, 0, 2, 3], ![1, 6, 4, 0, 3, 2], ![1, 5, 4, 3, 0, 2]], proof := .tail 97 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17966)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 3, 4], ![1, 6, 0, 5, 2, 4], ![1, 6, 5, 0, 2, 3], ![6, 1, 4, 0, 3, 2], ![5, 1, 4, 3, 0, 2]], proof := .tail 97 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17967)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 5, 3, 4], ![1, 6, 0, 5, 2, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 0, 3, 2], ![5, 4, 1, 3, 0, 2]], proof := .tail 1 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17968)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 6, 3, 4, 5, 0], ![1, 0, 6, 5, 3, 4], ![6, 1, 0, 5, 2, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 0, 3, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 1 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17969)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 3, 4, 6], ![1, 0, 5, 2, 4, 6], ![5, 1, 0, 2, 3, 6], ![4, 1, 0, 3, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 120 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17970)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 3, 4, 6], ![1, 0, 5, 2, 6, 4], ![5, 1, 0, 2, 6, 3], ![4, 1, 0, 3, 2, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 210 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17971)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 3, 6, 4], ![1, 0, 5, 2, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 0, 3, 2, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 17 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17972)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 3, 6, 4], ![1, 0, 5, 2, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 0, 3, 2, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 186 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17973)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 5, 3, 6, 4], ![1, 0, 5, 2, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 0, 3, 2, 6], ![4, 1, 0, 2, 3, 5]], proof := .low6 (![252, 119, 192, 201, 64, 157, 75, 163, 49, 12, 115, 238, 70, 26, 152, 46, 238, 72, 172, 220, 238, 113, 53, 238, 113, 179, 86, 238]) }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17974)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 6, 3, 4], ![1, 0, 5, 6, 2, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 0, 3, 2, 6], ![1, 0, 4, 3, 2, 5]], proof := .tail 249 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17975)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 5, 6, 2, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 0, 3, 6, 2], ![1, 0, 4, 3, 5, 2]], proof := .tail 185 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17976)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 2, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 0, 6, 3, 2], ![1, 0, 4, 5, 3, 2]], proof := .tail 59 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17977)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 6, 3, 4], ![1, 0, 5, 6, 2, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 0, 3, 2, 6], ![1, 4, 0, 3, 2, 5]], proof := .tail 249 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17978)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 5, 6, 2, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 0, 3, 6, 2], ![1, 4, 0, 3, 5, 2]], proof := .tail 185 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17979)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 2, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 0, 6, 3, 2], ![1, 4, 0, 5, 3, 2]], proof := .tail 59 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17980)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 2, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 0, 3, 2], ![1, 4, 5, 0, 3, 2]], proof := .tail 59 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17981)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 5, 6, 3, 4], ![1, 0, 5, 6, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 0, 3, 2, 6], ![4, 1, 0, 3, 2, 5]], proof := .low6 (![248, 31, 121, 81, 126, 200, 270, 134, 2, 92, 141, 123, 167, 158, 254, 141, 138, 138, 88, 170, 35, 42, 110, 191, 191, 16, 36, 218]) }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17982)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 5, 6, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 0, 3, 6, 2], ![4, 1, 0, 3, 5, 2]], proof := .tail 176 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17983)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 0, 6, 3, 2], ![4, 1, 0, 5, 3, 2]], proof := .tail 59 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17984)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 0, 3, 2], ![4, 1, 5, 0, 3, 2]], proof := .tail 59 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17985)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 0, 3, 2], ![4, 5, 1, 0, 3, 2]], proof := .tail 59 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17986)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 2, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 0, 3, 2], ![5, 4, 1, 0, 3, 2]], proof := .tail 55 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17987)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 6, 0, 5, 2, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 0, 3, 2], ![1, 4, 5, 3, 0, 2]], proof := .tail 68 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17988)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 5, 3, 4], ![1, 6, 0, 5, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 0, 3, 2], ![4, 1, 5, 3, 0, 2]], proof := .tail 68 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17989)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 6, 5, 3, 4], ![1, 6, 0, 5, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 0, 3, 2], ![4, 5, 1, 3, 0, 2]], proof := .tail 5 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17990)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 6, 5, 3, 4], ![1, 6, 0, 5, 2, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 0, 3, 2], ![5, 4, 1, 3, 0, 2]], proof := .tail 181 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17991)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 6, 3, 5, 4, 0], ![1, 0, 6, 5, 3, 4], ![6, 1, 0, 5, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 0, 3, 2], ![4, 5, 3, 1, 0, 2]], proof := .tail 68 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17992)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 6, 3, 5, 4, 0], ![1, 0, 6, 5, 3, 4], ![6, 1, 0, 5, 2, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 0, 3, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 132 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17993)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 3, 4, 6], ![1, 5, 0, 2, 4, 6], ![1, 5, 0, 2, 3, 6], ![1, 4, 3, 0, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 182 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17994)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 3, 4, 6], ![1, 5, 0, 2, 6, 4], ![1, 5, 0, 2, 6, 3], ![1, 4, 3, 0, 2, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 18 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17995)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 3, 6, 4], ![1, 5, 0, 2, 6, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 3, 0, 2, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 244 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17996)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 3, 4], ![1, 5, 0, 6, 2, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 3, 0, 2, 6], ![1, 0, 4, 3, 2, 5]], proof := .tail 125 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17997)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 5, 0, 6, 2, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 3, 0, 6, 2], ![1, 0, 4, 3, 5, 2]], proof := .tail 155 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17998)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![2, 5, 3, 6, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 3, 6, 4], ![1, 5, 0, 2, 6, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 3, 0, 2, 6], ![1, 4, 0, 2, 3, 5]], proof := .low6 (![156, 259, 112, 208, 64, 157, 146, 160, 268, 149, 217, 238, 33, 98, 160, 160, 238, 160, 6, 51, 238, 43, 204, 238, 195, 179, 202, 238]) }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17999)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![2, 5, 3, 6, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 3, 4], ![1, 5, 0, 6, 2, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 3, 0, 2, 6], ![1, 4, 0, 3, 2, 5]], proof := .tail 236 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18000)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![2, 5, 3, 6, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 5, 0, 6, 2, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 3, 0, 6, 2], ![1, 4, 0, 3, 5, 2]], proof := .tail 11 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18001)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 3, 4], ![1, 5, 6, 0, 2, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 3, 0, 2, 6], ![1, 4, 3, 0, 2, 5]], proof := .low6 (![269, 190, 83, 255, 154, 200, 14, 151, 178, 106, 117, 23, 23, 273, 73, 245, 245, 245, 153, 261, 213, 213, 225, 258, 10, 102, 117, 203]) }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18002)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 5, 6, 0, 2, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 3, 0, 6, 2], ![1, 4, 3, 0, 5, 2]], proof := .tail 176 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18003)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 5, 6, 0, 2, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 3, 6, 0, 2], ![1, 4, 3, 5, 0, 2]], proof := .tail 171 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18004)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 6, 5, 0, 2, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 6, 3, 0, 2], ![1, 4, 5, 3, 0, 2]], proof := .tail 93 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18005)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 6, 5, 0, 2, 4], ![1, 6, 5, 0, 2, 3], ![1, 6, 4, 3, 0, 2], ![1, 5, 4, 3, 0, 2]], proof := .tail 214 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18006)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 3, 4], ![1, 6, 5, 0, 2, 4], ![1, 6, 5, 0, 2, 3], ![6, 1, 4, 3, 0, 2], ![5, 1, 4, 3, 0, 2]], proof := .tail 57 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18007)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 5, 3, 4], ![1, 6, 5, 0, 2, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 3, 0, 2], ![5, 4, 1, 3, 0, 2]], proof := .tail 21 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18008)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 6, 3, 4, 5, 0], ![1, 0, 6, 5, 3, 4], ![6, 1, 5, 0, 2, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 3, 0, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 234 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18009)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 3, 4, 6], ![1, 5, 0, 2, 4, 6], ![5, 1, 0, 2, 3, 6], ![4, 1, 3, 0, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 182 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18010)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 3, 4, 6], ![1, 5, 0, 2, 6, 4], ![5, 1, 0, 2, 6, 3], ![4, 1, 3, 0, 2, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 187 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18011)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 3, 6, 4], ![1, 5, 0, 2, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 3, 0, 2, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 61 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18012)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![2, 5, 3, 6, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 3, 6, 4], ![1, 5, 0, 2, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 3, 0, 2, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 142 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18013)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![2, 5, 3, 6, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 5, 3, 6, 4], ![1, 5, 0, 2, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 3, 0, 2, 6], ![4, 1, 0, 2, 3, 5]], proof := .low6 (![275, 119, 192, 266, 64, 157, 146, 94, 49, 109, 115, 238, 209, 26, 152, 46, 238, 211, 172, 220, 238, 82, 22, 238, 195, 179, 202, 238]) }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18014)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 6, 3, 4], ![1, 5, 0, 6, 2, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 3, 0, 2, 6], ![1, 0, 4, 3, 2, 5]], proof := .tail 90 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18015)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![2, 5, 3, 6, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 6, 3, 4], ![1, 5, 0, 6, 2, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 3, 0, 2, 6], ![1, 4, 0, 3, 2, 5]], proof := .tail 249 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18016)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![2, 5, 3, 6, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 5, 6, 3, 4], ![1, 5, 0, 6, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 3, 0, 2, 6], ![4, 1, 0, 3, 2, 5]], proof := .tail 90 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18017)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 5, 0, 6, 2, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 3, 0, 6, 2], ![1, 0, 4, 3, 5, 2]], proof := .tail 11 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18018)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![2, 5, 3, 6, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 5, 0, 6, 2, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 3, 0, 6, 2], ![1, 4, 0, 3, 5, 2]], proof := .tail 11 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18019)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![2, 5, 3, 6, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 5, 3, 4], ![1, 5, 0, 6, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 3, 0, 6, 2], ![4, 1, 0, 3, 5, 2]], proof := .tail 11 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18020)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 6, 3, 4], ![1, 5, 6, 0, 2, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 3, 0, 2, 6], ![1, 4, 3, 0, 2, 5]], proof := .tail 237 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18021)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 5, 6, 0, 2, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 3, 0, 6, 2], ![1, 4, 3, 0, 5, 2]], proof := .tail 185 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18022)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 5, 6, 0, 2, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 3, 6, 0, 2], ![1, 4, 3, 5, 0, 2]], proof := .tail 135 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18023)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 3, 4], ![1, 6, 5, 0, 2, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 3, 0, 2], ![1, 4, 5, 3, 0, 2]], proof := .tail 93 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18024)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 5, 6, 3, 4], ![1, 5, 6, 0, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 3, 0, 2, 6], ![4, 1, 3, 0, 2, 5]], proof := .low6 (![177, 118, 166, 255, 114, 200, 14, 107, 221, 229, 45, 198, 198, 139, 0, 165, 38, 41, 66, 137, 29, 219, 225, 258, 216, 102, 222, 203]) }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18025)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 5, 3, 4], ![1, 5, 6, 0, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 3, 0, 6, 2], ![4, 1, 3, 0, 5, 2]], proof := .tail 176 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18026)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 5, 3, 4], ![1, 5, 6, 0, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 3, 6, 0, 2], ![4, 1, 3, 5, 0, 2]], proof := .tail 171 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18027)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 5, 3, 4], ![1, 6, 5, 0, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 3, 0, 2], ![4, 1, 5, 3, 0, 2]], proof := .tail 93 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18028)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 6, 5, 3, 4], ![1, 6, 5, 0, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 3, 0, 2], ![4, 5, 1, 3, 0, 2]], proof := .tail 233 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18029)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 6, 5, 3, 4], ![1, 6, 5, 0, 2, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 3, 0, 2], ![5, 4, 1, 3, 0, 2]], proof := .tail 71 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18030)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 6, 3, 5, 4, 0], ![1, 0, 6, 5, 3, 4], ![6, 1, 5, 0, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 3, 0, 2], ![4, 5, 3, 1, 0, 2]], proof := .tail 242 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18031)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 6, 3, 5, 4, 0], ![1, 0, 6, 5, 3, 4], ![6, 1, 5, 0, 2, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 3, 0, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 234 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18032)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 5, 3, 4, 6], ![5, 1, 0, 2, 4, 6], ![5, 1, 0, 2, 3, 6], ![4, 3, 1, 0, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 182 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18033)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 5, 3, 4, 6], ![5, 1, 0, 2, 6, 4], ![5, 1, 0, 2, 6, 3], ![4, 3, 1, 0, 2, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 62 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18034)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 5, 3, 6, 4], ![5, 1, 0, 2, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 3, 1, 0, 2, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 206 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18035)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![2, 5, 3, 6, 4, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 5, 3, 6, 4], ![5, 1, 0, 2, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 1, 0, 2, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 197 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18036)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![2, 5, 3, 6, 4, 1], ![2, 5, 3, 6, 4, 0], ![1, 0, 5, 3, 6, 4], ![5, 1, 0, 2, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 1, 0, 2, 6], ![4, 1, 0, 2, 3, 5]], proof := .low6 (![276, 119, 79, 8, 64, 157, 270, 13, 49, 12, 115, 238, 65, 26, 152, 46, 238, 67, 164, 274, 238, 99, 63, 238, 199, 179, 247, 238]) }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18037)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 5, 6, 3, 4], ![5, 1, 0, 6, 2, 4], ![5, 1, 0, 6, 2, 3], ![4, 3, 1, 0, 2, 6], ![1, 0, 4, 3, 2, 5]], proof := .tail 150 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18038)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![2, 5, 3, 6, 4, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 5, 6, 3, 4], ![5, 1, 0, 6, 2, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 1, 0, 2, 6], ![1, 4, 0, 3, 2, 5]], proof := .tail 150 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18039)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![2, 5, 3, 6, 4, 1], ![2, 5, 3, 6, 4, 0], ![1, 0, 5, 6, 3, 4], ![5, 1, 0, 6, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 1, 0, 2, 6], ![4, 1, 0, 3, 2, 5]], proof := .tail 212 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18040)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![2, 5, 3, 4, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 6, 5, 3, 4], ![5, 1, 0, 6, 2, 4], ![5, 1, 0, 6, 2, 3], ![4, 3, 1, 0, 6, 2], ![1, 0, 4, 3, 5, 2]], proof := .tail 264 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18041)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![2, 5, 3, 6, 4, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 6, 5, 3, 4], ![5, 1, 0, 6, 2, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 1, 0, 6, 2], ![1, 4, 0, 3, 5, 2]], proof := .tail 264 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18042)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![2, 5, 3, 6, 4, 1], ![2, 5, 3, 6, 4, 0], ![1, 0, 6, 5, 3, 4], ![5, 1, 0, 6, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 1, 0, 6, 2], ![4, 1, 0, 3, 5, 2]], proof := .tail 264 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18043)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 5, 6, 3, 4], ![5, 1, 6, 0, 2, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 1, 0, 2, 6], ![1, 4, 3, 0, 2, 5]], proof := .tail 194 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18044)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 6, 5, 3, 4], ![5, 1, 6, 0, 2, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 1, 0, 6, 2], ![1, 4, 3, 0, 5, 2]], proof := .tail 136 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18045)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 5, 3, 4, 6, 0], ![1, 0, 6, 5, 3, 4], ![5, 1, 6, 0, 2, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 1, 6, 0, 2], ![1, 4, 3, 5, 0, 2]], proof := .tail 84 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18046)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 5, 3, 6, 4, 0], ![1, 0, 5, 6, 3, 4], ![5, 1, 6, 0, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 1, 0, 2, 6], ![4, 1, 3, 0, 2, 5]], proof := .tail 58 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18047)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (17920 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 17920 ≤ id.val) (hhigh : id.val < 18048) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 17920)) = true := by
  let j : Fin 128 := ⟨id.val - 17920, by omega⟩
  have hsum : 17920 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (17920 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard140
