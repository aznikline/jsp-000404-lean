import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard141
open N4R2RowDataReplay

-- Original cycle 0119cf9eba25cb14f9f7b3011d28979ea22422028be9378818f34474a1ef4ff3; original global index 97.
def localCycle00000 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .triangle 11 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 01a7d77754e23fadcc721af938b9c78fac26297519ae3bb62baccd42102f08ec; original global index 135.
def localCycle00001 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 11 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 022bc14e0c31fcb70ac2d503c2faa80b16bc288803b926d410f955f0c8d64fa2; original global index 173.
def localCycle00002 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 0 6, .distance 0 3, .distance 0 2]
    constant := ![2, 0, 0, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, true, false] }
  origin := ![.gapUpper 2 2, .triangle 8 2, .triangle 11 1, .gapLower 0 1]

-- Original cycle 026a995f048689c8617c2383e3842584b63c6ca2c0fcc217b8cacc02250b6bba; original global index 190.
def localCycle00003 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![-2, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 5, .gapLower 0 4, .gapLower 4 2, .triangle 23 2, .gapUpper 1 5]

-- Original cycle 02fb9e5cecbb9c213a8c1f81f9e6f503a88ae654a3e9f849b08ad989038b898d; original global index 240.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 4 6, .distance 1 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .gapLower 6 3, .triangle 23 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 030559f867b6b9d1e5141ae75403446476aaeb0786373ffc752701c7d0f12ceb; original global index 242.
def localCycle00005 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 4, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 056df7eba7acfd9e5231b6915ab6e6cc87edb7d1d64c86205122e4cfbcff22b0; original global index 442.
def localCycle00006 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 6, .distance 0 5, .theta 0, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, 0, 0, -2, -1, 2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]
    strict := ![false, false, false, true, false, true, true, false, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 32 0, .triangle 34 1, .triangle 14 2, .gapLower 0 4, .corridorLower 0 5, .gapLower 0 6, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 05c2e7a2dfbef84b24c7fe857ce7916703856b1aeb4de8f1b30913c2f2c4a2a3; original global index 477.
def localCycle00007 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 061dfbd8e51f32209bf2880a858cc1d1a26ef13d6b5ceb09b63afbc2fa9e6c54; original global index 505.
def localCycle00008 : Cycle where
  length := 3
  data := {
    node := ![.theta 0, .distance 0 1, .theta 1, .theta 0]
    constant := ![2, -2, 0]
    coefficient := ![1, -1, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 6, .gapUpper 1 6, .thetaNext 0]

-- Original cycle 067bdd2b37b8a410843463cab93e3e4eb0a2890b6af3f03ec61b2a60a1daacb6; original global index 532.
def localCycle00009 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 4 6, .distance 0 6, .distance 1 6, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .gapLower 6 3, .gapLower 6 2, .triangle 4 1, .triangle 21 1, .gapLower 3 0]

-- Original cycle 06a24465f2cc7199dc48e92b47798e638731fc38a389af4d877ec5083eccc496; original global index 546.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 14 1, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 07100cbe918dea0b82a15749ecf41d299639eb5b99474d1a90fec91ce1c08eb3; original global index 580.
def localCycle00011 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 07af1e31c676357f503d6c0ecfa973b6112fd3acc7a5349278fbce470064a5cb; original global index 626.
def localCycle00012 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -2, -1, 2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 1, -1, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .gapLower 0 3, .corridorLower 0 4, .gapLower 0 6, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 091d6dc2f04385426b22aabbe8436ca3895cf8badd49f0bf8313c6a230925295; original global index 727.
def localCycle00013 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 10 1, .gapLower 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 093eac8eaef2132deeb7771ec956152b6de52927bc8a8359b75c1ec97d9f7613; original global index 738.
def localCycle00014 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle 095800b454161b7d4f75e17a91d04de918e39c915343f1a7fec0fd810f25383b; original global index 745.
def localCycle00015 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 5, .distance 1 5, .distance 1 2, .theta 1]
    constant := ![3, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .gapLower 0 4, .gapLower 5 1, .triangle 17 1, .corridorLower 1 2]

-- Original cycle 0984138f5f8d1d8327abfcff7c2ccdc4745fd507a29724ecf06a289ee5ffbda7; original global index 756.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 09b447c9dd31b4e590ce0303643a12793f9029ad7d029f26f6b0b12848b99e6e; original global index 774.
def localCycle00017 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 30 0, .gapLower 6 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 09b7f80ef696a38f10b551d18bfc4877f7bc19a715d7fac9735446f4e1bc9d75; original global index 776.
def localCycle00018 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.gapUpper 2 2, .gapLower 4 3, .gapLower 4 2, .gapLower 0 2, .gapLower 0 1]

-- Original cycle 0a9240c5f6198e3c21b72e64f407b29e8e96c56b92ba252edb6e0c0d9fca7157; original global index 842.
def localCycle00019 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 34 0, .triangle 24 0, .triangle 20 1, .gapLower 3 0]

-- Original cycle 0b28a83c3b72e71c5cdbe76164a0f4f1bfc8542d6f7843a975b1deb52d7e8cfc; original global index 893.
def localCycle00020 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 32 0, .corridorLower 4 6]

-- Original cycle 0c19f1247b41407eab71c4b53be3393f33a18ab14543afb1cfc4c6f2c183ec81; original global index 957.
def localCycle00021 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .gapLower 4 3, .triangle 13 0, .triangle 23 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 0cb2849d54225f201d2b8606e9879ffacbce87266902f6d878dbb5947e2cda0f; original global index 1006.
def localCycle00022 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .gapLower 6 3, .triangle 14 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 0ccdab088c5038e8d2a050b5a208a5b1fef9a7d1fef43940d22c7f387679cfbf; original global index 1014.
def localCycle00023 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 2 4]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 29 1]

-- Original cycle 0d2151388107e667b614b6730c1edc825c223ec2ba3a4291aac4f3ec02580f06; original global index 1043.
def localCycle00024 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 11 2, .triangle 14 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle 0d654c4bdaae5a05a2b6e7990d144e5fb40ac442f9991562d0abdf320a61beb9; original global index 1059.
def localCycle00025 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 4, .distance 1 4, .theta 1]
    constant := ![3, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .gapLower 0 4, .gapLower 4 2, .corridorLower 1 4]

-- Original cycle 0db3ef377bb925b9a51e3ddf11787b1e4acb1803d042cec5132175a31445bc92; original global index 1083.
def localCycle00026 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 3, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 0e1c7881ae1c00fc529f650e4478fb60a1263e2b941655789a33c0eb21475fb1; original global index 1113.
def localCycle00027 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 6, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -2, -2, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.triangle 2 2, .triangle 13 2, .gapLower 6 2, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle 0e307303a4a75df1c4f6b22eb7279a2f58e6a0982e9093b3a8ea29a0ec8743d6; original global index 1117.
def localCycle00028 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 3]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 3 2, .triangle 11 2, .gapLower 0 2]

-- Original cycle 0e5cd6667543c54d97767939f453cd4bf8ea6a1176aaafd48e6add191efd5a1b; original global index 1136.
def localCycle00029 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -2, -2, 0, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, true, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .gapLower 6 2, .gapLower 6 1, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 0e6418eb9e5be0a4bba6460da612bce306b01b22dfa76ab05aa4111151222cac; original global index 1138.
def localCycle00030 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 1 5, .distance 0 1]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 3 1, .gapUpper 1 5]

-- Original cycle 0e8ca9ea15a287cf4c98afb8eb09dde332003b2cac79c151e40c52d8de86f438; original global index 1149.
def localCycle00031 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 0ea29633a3a2fd0bba1905c215b049014d2ee17610df510cbf4a3481ef5f7ab7; original global index 1156.
def localCycle00032 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 2 6, .distance 2 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 29 1]

-- Original cycle 0f8897c4b60fe4c6ad93d07bc686402ca7e64e73fbd34b916f8aadc13ecfa26b; original global index 1237.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .gapLower 5 3, .gapLower 0 4, .triangle 13 0, .triangle 23 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 113e244e5c1d29302933907bc476674e33bf39a882a88f85d453eda9e1a303b0; original global index 1368.
def localCycle00034 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.gapUpper 2 2, .triangle 29 1, .triangle 32 0, .triangle 9 0, .triangle 5 1]

-- Original cycle 113e6edf5185083f5ea3caf88b0884598f8fdd89b5dfa32d114f967659f5031a; original global index 1369.
def localCycle00035 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 11de3e14dfd97f7c37e87247177627377bb530bfe7d8bd5be6d7cefe71ccd0a1; original global index 1427.
def localCycle00036 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 0 5, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 7 2, .triangle 14 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 12f1fedba2062d1c54be80b848c1797ecc07d3dc3eae78902bac7ad9391b6914; original global index 1491.
def localCycle00037 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 18 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 1459ac9c4543ab442b205c8a9e1b0e4945ac10be3dd068cef4135b53c8f47bdf; original global index 1606.
def localCycle00038 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 6, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -3, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .gapLower 5 3, .gapLower 0 4, .triangle 13 1, .triangle 9 1, .triangle 5 1, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 145b7f5f8d76ac195ee285145d7555e904a7ef715fa24be23cc0d4e99fbc6ed0; original global index 1608.
def localCycle00039 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -1, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true, true] }
  origin := ![.gapUpper 2 2, .triangle 30 1, .triangle 33 0, .triangle 31 1, .triangle 12 0, .triangle 9 1, .triangle 5 1]

-- Original cycle 146a71bc717f5bcd4e19c4a19103590120a6866c985a35b33e0279db32eaa375; original global index 1612.
def localCycle00040 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 3 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 1, .gapLower 6 3, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 14709a6bcd0fef68d9fe6b3efc8f2e98336b57d35163a6a681e0bfe3fbd2b67e; original global index 1617.
def localCycle00041 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .gapLower 6 3, .triangle 23 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 159dca7dcb69a1bb93a8c074255b07b32d8b60fd85c9d4b10b878c90b13a25da; original global index 1713.
def localCycle00042 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .gapLower 4 2, .gapLower 0 2, .triangle 5 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 16420727fde9801009558d494b45859374d9aca618547125b8e4afc781f10b92; original global index 1754.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 5, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 2, .triangle 14 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 16d92797fd6df4ae24f5a43792fb52554be93b794b8ceaec26b68a235abefe11; original global index 1797.
def localCycle00044 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 11 2, .triangle 13 1, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 177a2f705819c3079d5ac1791fbf76e686559dd49de7ce2fda31ba890b74d7e7; original global index 1838.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 178dd02c03f14404bcfd07c548759093d9e4d1a9f44d1be68ae49d0b3dd27920; original global index 1842.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 3 6, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 32 2, .triangle 11 0, .triangle 5 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 1801ccc9cce756add6edd5a90e7f14c53fc5c0a5233ad4eefa2f17883eeb8ac4; original global index 1876.
def localCycle00047 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 1, 0, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 29 0, .triangle 6 2, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 1822c49002cf57412d389cf223f114bb73c173e2fa748de3fbeb316f13c17cc9; original global index 1888.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .gapLower 6 2, .triangle 13 1, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 194d1a9a69a3d2826a4830801bcd476092d208c902d2913f392f60c6be25aaf5; original global index 1978.
def localCycle00049 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 2 3]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 2 4, .gapUpper 4 5, .gapLower 6 4, .triangle 27 0]

-- Original cycle 1ab19d11244a344c3fb5db216cc9fa09e5b0b0ee06d2faf7ede08955a1d92a96; original global index 2076.
def localCycle00050 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .gapLower 6 3, .triangle 23 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 1b5d7533eb79e83e719e2dee5171059c270f95504c5f6168fcdcb06fd1a4330b; original global index 2120.
def localCycle00051 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 1c0e11b54e5c0d8cdc7aeb1ae60966219df3149f4141c4fe20e90d9b293c4e06; original global index 2166.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 4, .distance 4 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 2, .triangle 13 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 1c941595e4fc303e903c4f20b1c413fb8280ad5ac71d366ec85087e283d33453; original global index 2201.
def localCycle00053 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 18 2, .gapLower 6 2, .corridorLower 3 6, .thetaLower 3]

-- Original cycle 1ccfa76289af828de3ddd534604e50483a15a91df79a0e170603036139322292; original global index 2215.
def localCycle00054 : Cycle where
  length := 5
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 2, .triangle 8 2, .gapLower 6 1, .gapLower 6 0]

-- Original cycle 1cd44a0ac6fb707c5d00829afa1b9a30bb568f867357d3175eccf17237868487; original global index 2217.
def localCycle00055 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .theta 0]
    constant := ![2, -1, -1, -1, 3, -1, -1, -1, 0, -2]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 6, .triangle 3 0, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 13 0, .triangle 6 1, .gapLower 0 0]

-- Original cycle 1ced8e4dbb1b81865f15a7ae00e9acbfeeee1cb264e7cb23fdccf951023257a8; original global index 2231.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 1, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 1ddf5b73eaad4d618a7b44f11e7b08055592c3309f2de2a631b7aeb4b95f3f99; original global index 2295.
def localCycle00057 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 1, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle 1e8d267cac6d2a6d35246ef957a488cef295f3c36796162f12f202e7214c4b73; original global index 2346.
def localCycle00058 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 8 2, .gapLower 6 2, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 1ec84ef5d46670f7d3c074fbf136fccd8250e2e4e5c0a3ca7049b1e5edbd4c8a; original global index 2363.
def localCycle00059 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 4 1, .gapUpper 1 5]

-- Original cycle 1ed6401c6bfa9e50fc8c89ccc95345db90e907358d26e11d431c9598ad864c7e; original global index 2367.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 0 6, .distance 1 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .gapLower 6 3, .triangle 21 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 1f00633f9980f14d225fcd739776f76239704fe6cbbba22238edec74e33c1926; original global index 2379.
def localCycle00061 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 5, .distance 0 4, .distance 1 4, .theta 1]
    constant := ![3, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 4 2, .gapLower 0 4, .gapLower 0 3, .gapLower 4 1, .corridorLower 1 4]

-- Original cycle 2051684e2ed44527b71aaf78ca915f711db5f253b1436dbd44d82080fdeb200e; original global index 2477.
def localCycle00062 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![-2, 0, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true] }
  origin := ![.gapLower 0 5, .triangle 12 1, .triangle 13 0, .triangle 23 2, .gapUpper 1 5]

-- Original cycle 205437bd43aac86da3ca1ca753617d4f14b0a35da9c5887ed3b5971f7e42e852; original global index 2479.
def localCycle00063 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 207d561e806c46ca59014524d40518d4e6932adfa602d662886a62fb13c482bb; original global index 2493.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 11 2, .triangle 4 1, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 208574011ef64e49fb85678aa0cda82989e4555436f6d379a1477f0465c2279b; original global index 2496.
def localCycle00065 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![4, 0, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 21 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 20b500e188f2ecf7e8974dbe2d601774de5bfe596d8cee81999509ab173326c7; original global index 2507.
def localCycle00066 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 20bf5ef557cebe41e35bbd669600d71916143afeda2f3d51fcd10ddc99ce6a72; original global index 2509.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![4, -1, 0, -3, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .gapLower 5 3, .gapLower 0 4, .triangle 13 0, .triangle 23 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 214740365bbd99125a55b640ab30f0df281dfbb91996fc9ce37b42731c40b636; original global index 2550.
def localCycle00068 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 21766cdd929a0fd5e316138034ef33dd4b3cbb6fde8573dc59f9ff67a7acdf21; original global index 2562.
def localCycle00069 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 1 6, .distance 1 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 1, .gapLower 6 1, .triangle 24 1]

-- Original cycle 21c7d9de6a9daae046d71287913cb29f1fc45129969065f4c317fc85420a5714; original global index 2590.
def localCycle00070 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .triangle 24 0, .triangle 20 1, .gapLower 3 0]

-- Original cycle 229e9d3fe8aa4dd914b701781949f5592116763b46d10d7cb8e72acc90c9f41f; original global index 2648.
def localCycle00071 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .gapLower 6 3, .corridorLower 5 6]

-- Original cycle 23aebbf311118533adce49ab122728d3a4c4896dff3cfa0171d594c142c8de18; original global index 2737.
def localCycle00072 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -1, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 2 2, .gapLower 4 3, .triangle 9 0, .gapLower 0 1]

-- Original cycle 23fef1cd68727cc73dbc0ad2b19309bdd4390090aaa4f8508c958baf55f021c3; original global index 2756.
def localCycle00073 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![4, 0, -1, -1, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 4 6, .gapLower 5 5, .triangle 26 0, .triangle 27 0, .gapLower 6 3, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 24b729c9f9f3c7c6a8781a9aaf997024973c6c5c32c1bae66df012317a8557bc; original global index 2816.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 30 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 258a99c6ba4862c5078120098eb305586189b839a17d477e4674cea2ba4e6c1a; original global index 2885.
def localCycle00075 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 2599a86d7a075e0d205d5d4266519f382bfe14823b5d84385bbe1aa04a2520ef; original global index 2890.
def localCycle00076 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, 0, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle 2659017c40309a02b8ecb144f9821c7e7f3bee2677ea89c728530385577ce570; original global index 2945.
def localCycle00077 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1]
    constant := ![3, -2, 0, -1, -1, 0, 2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .triangle 12 1, .triangle 13 0, .triangle 23 0, .gapLower 1 2, .gapUpper 3 1, .gapLower 0 1, .gapLower 2 1, .corridorLower 1 2]

-- Original cycle 26788f88dc66d8061782259edd5b67c8e5980aad6a274bbe0786995e7c6d0a22; original global index 2954.
def localCycle00078 : Cycle where
  length := 4
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .theta 6]
    constant := ![3, -2, 0, -2]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 23 2, .gapLower 6 0]

-- Original cycle 27f02079afb8d8e40ebdd0b8b4d067f6303e63f8d2b3c14f0cce6e1a06d558ab; original global index 3056.
def localCycle00079 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 28f3a66b963c04189804d2ff66514753fc78ebcf81c9a717712ac91f42df9729; original global index 3131.
def localCycle00080 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 3 6, .distance 5 6, .distance 3 5]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 33 2, .gapLower 6 3, .gapUpper 5 3]

-- Original cycle 28f4f224c7451865986ff8f42c49951aca4e3b9df9da0563ada06a04ced5bc9b; original global index 3132.
def localCycle00081 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 21 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 291d210e121858fbe5d9ada453f83d2bb3bc9b3a84ac94cd7d4b79352622831e; original global index 3140.
def localCycle00082 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![4, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 19 0, .triangle 21 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 2938da42efd1292e6ea723e94f58a082fb73c293a8fd295b47cf4b5e90a30810; original global index 3145.
def localCycle00083 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 3 6, .distance 4 6, .distance 3 4]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 32 2, .gapLower 6 3, .gapUpper 4 4]

-- Original cycle 298ec2dad45665bd56e18f3386a751d8f782e941290493b50c509887f1148346; original global index 3170.
def localCycle00084 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 2 4]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 2 3, .gapUpper 5 5, .gapLower 6 5, .triangle 29 0]

-- Original cycle 29fcdd87ffc7aaaed82324171a7c5e9001514c33ca504a66b2eadcc2bb5a90c9; original global index 3202.
def localCycle00085 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaLower 1]

-- Original cycle 2b0f0504a4d3c658ddc9be80951d31b6951e5388f63056404abf3ec08b6d037a; original global index 3289.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .gapLower 6 3, .triangle 13 1, .triangle 23 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 2b10631e03e67b79ea89f73257271756899d8de9971d343db8000cc4e1ceb8a3; original global index 3290.
def localCycle00087 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaLower 1]

-- Original cycle 2b90d17c2912df76007e0510ee2955fe5acd0524b77b5e77f9f5f139850a5d9f; original global index 3328.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, 0, -1, -1, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle 2c4b1f74762e9d03e49cd626ea765c9e4add6d53ee4f9935954a63ae7b66b052; original global index 3388.
def localCycle00089 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 5 6, .theta 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, -1, 0, -2, -2, 0, 3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 2cc74389dce35112061875c3898df16dcc0ad78ef7905edeee4e29d045095d54; original global index 3419.
def localCycle00090 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .gapLower 6 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 2d3fc4530e2201afcc31dde8026bdcb31dfdecae6c33f1330fbe31f66da6e645; original global index 3454.
def localCycle00091 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 13 2, .gapLower 6 2, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaNext 0, .thetaLower 0]

-- Original cycle 2d942570c5ab7b6d73c630b81823f53d7363c69367e200d6e27b161c5984543d; original global index 3472.
def localCycle00092 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 5 2, .triangle 14 2, .gapLower 0 4]

-- Original cycle 2e01a496f1190a505f12ae50fb9cd78d9e9a5ccbffa51186b86c1e6ffcbc0347; original global index 3512.
def localCycle00093 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 6, .distance 4 6, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, -1, -1, -2, 2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 24 0, .gapLower 6 0, .gapLower 6 6, .triangle 29 0, .triangle 16 0, .corridorLower 1 2]

-- Original cycle 2e10275cd8ab16834f633c862a818fc7130be5ec9688f0c72cdf9670e1036f84; original global index 3520.
def localCycle00094 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 8 2, .triangle 13 1, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 2f05fe452166c56dddf94dba70d1cda9b6d6201a1e0bee481ab58948d574aef9; original global index 3596.
def localCycle00095 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![0, 0, 2, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 4 2, .triangle 34 1, .gapUpper 5 2, .gapLower 0 4]

-- Original cycle 30406780557f7d32cb80e076280f7ef8fb6cbb40ac2c37e8f191ea50d3c686a4; original global index 3672.
def localCycle00096 : Cycle where
  length := 3
  data := {
    node := ![.theta 0, .distance 0 1, .theta 1, .theta 0]
    constant := ![1, -2, 0]
    coefficient := ![1, -1, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 6, .gapUpper 1 6, .thetaNext 0]

-- Original cycle 306e1f07b62ee89723d0508806be96493d6038f07369090e79e0cd6fc3d47cbb; original global index 3687.
def localCycle00097 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 3075ee2af60f21abedf51a7825373af0ccc6cde2c21c1c4acc89c872901242b2; original global index 3689.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 31b7b1e50c47c7db0f13defc7ed82880dbf2371ba083dc186c72f39ff76bf658; original global index 3798.
def localCycle00099 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .gapLower 6 4, .triangle 11 2, .triangle 14 1, .triangle 24 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 31bf864b18620fab1532155a25def878168cad74ed079fbba75e18a74eef3271; original global index 3799.
def localCycle00100 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 33 1, .gapLower 5 2, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 3214b5ef0599005eb1973cb6a5b44b65b7911cd8eca9f7a1f8ab3161ab66c26d; original global index 3824.
def localCycle00101 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .gapLower 6 2, .gapLower 6 1, .triangle 21 1, .gapLower 3 0]

-- Original cycle 32223b4208cbe7c5e05e2d89187aaa28ec3179c922e37eef57b4a9ae81f9e16c; original global index 3828.
def localCycle00102 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .triangle 11 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 33a1a66f7afaf9ccc360b25f0599eac504708edbd426b10b895d403de3356d6e; original global index 3950.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 8 2, .triangle 14 1, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 33c229e44d481a9b380b1f7e82c61bc2ae3e32eafc683c5ac499033460d1a66f; original global index 3968.
def localCycle00104 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![4, 0, -1, -1, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 31 2, .triangle 26 0, .triangle 27 0, .gapLower 6 3, .gapLower 6 2, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 34941e378a29d3081f4b67002281a564e2a4b760f59eb6dc0e2d06d3a39400bb; original global index 4024.
def localCycle00105 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 7 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 35574ce519b0a1ea69615a3aca089042b47af89843c7e8f949d63dc879844826; original global index 4086.
def localCycle00106 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 4 2, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle 357c80aa309b1a5bacd4451d50bc804165c9e466bfd3fb66be09396e5d6c4f2b; original global index 4098.
def localCycle00107 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 4, .distance 0 3, .theta 0, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -2, -1, 2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .gapLower 4 2, .gapLower 0 2, .corridorLower 0 3, .gapLower 0 6, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 37350f75d31be93342d98404f31501f32968c3fdf30d95fb32525143b990aa64; original global index 4238.
def localCycle00108 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 4 2, .triangle 34 1, .gapLower 5 2, .gapLower 0 3]

-- Original cycle 388da610600a819ccf40ddf49849f58a10b1175fde0a6e038e68e92fd5754d38; original global index 4352.
def localCycle00109 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 393f5dce4c35096d60baa06bd8dfa71374b39ca36f6518231c17a82160d4651c; original global index 4404.
def localCycle00110 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 4 6, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 34 1]

-- Original cycle 3943ddeaaa72045b2642235b1e97f3040e57b7c1c4278c8015136cd52037c3ce; original global index 4405.
def localCycle00111 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 4, .distance 0 3]
    constant := ![2, 0, 0, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, true, false] }
  origin := ![.gapUpper 3 2, .triangle 11 2, .triangle 13 1, .gapLower 0 2]

-- Original cycle 3af4958d4c549d0cfea13daed05cd0d270e5b0b2ace48b8ef634b181d969ef39; original global index 4552.
def localCycle00112 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 3b06ad2d86b9d10a5cf79e675dc3fc0a863f3a47067e510c14dd03cece0760c8; original global index 4559.
def localCycle00113 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 2 6, .distance 2 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .triangle 27 1]

-- Original cycle 3b639125ab477d709389d3e67a2c451f6d5d789d3fac573a0149bf1b7d9a158c; original global index 4591.
def localCycle00114 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 3ba86a5e3ef128e450c80f359a195989a22e90b2ad087b14587c7d9b6d19c364; original global index 4613.
def localCycle00115 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 4, .distance 0 3]
    constant := ![2, 0, -2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 3 2, .triangle 11 2, .gapLower 0 3, .gapLower 0 2]

-- Original cycle 3bcc6240f5d0822f2557faa1bab006e558ef92e8508e07daa6ec18f5190aa7fd; original global index 4627.
def localCycle00116 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![3, -1, -1, -2, 2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .gapLower 6 0, .gapLower 6 6, .triangle 30 0, .triangle 17 0, .corridorLower 1 2]

-- Original cycle 3c20fa31453edf9a44371e48ae30f3cca538002e6179f976f8b53c4aa99ddf88; original global index 4661.
def localCycle00117 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 3d0611dce37c6a87abe1d39b6bffe4a722580ec4f429c6ed2c2b84e6bc04db85; original global index 4725.
def localCycle00118 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 3d9201047a9601a34bb78a4f33051731afe0b505f0730b820c1acc859f4d9d2c; original global index 4766.
def localCycle00119 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 4 6, .distance 2 6, .distance 2 5]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 30 1]

-- Original cycle 3d93ac90057f6c0f8bfb0725d45b5410e6ac949eac5d595b019cc977928d7858; original global index 4767.
def localCycle00120 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 8 2, .gapLower 6 1, .gapLower 6 0]

-- Original cycle 3dc55e1dcd3f1f2b9316350e702e64a65f7953465e3260943991d81e955c1af1; original global index 4782.
def localCycle00121 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 3e16c76a8f709d9c405a6fbc27c8d21a09f73a6eb0c399de2eda53780684db0b; original global index 4802.
def localCycle00122 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .gapLower 4 3, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 3e4d1bf524bf9521241b38f15345cd252a1189de526ce9ff7f65288e2cced2ba; original global index 4819.
def localCycle00123 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 2, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 3eef8321d0eac7e2c91b0e93b94d96db9c00128b320ce6b4c6c529709904acc8; original global index 4864.
def localCycle00124 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1]
    constant := ![3, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .triangle 10 1, .gapLower 0 1, .gapLower 2 1, .corridorLower 1 2]

-- Original cycle 3fc65694d829dfd7fe63baaafbcef46c262a959b314e4eec72e3e135a9431675; original global index 4927.
def localCycle00125 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 9 2, .triangle 12 0, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 3fe327a27eec79d758f53e1224e71b0913ef90c2378235cfc8b4b4d9ff1e2739; original global index 4932.
def localCycle00126 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .corridorLower 3 6]

-- Original cycle 40fa3b00b7dada6743aee53cc312443dc701f38c385a166357449bf955dcfff5; original global index 5019.
def localCycle00127 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 420de4cf93985dfc6930d75173bad97fc735a8e8ecce84ef02950a21a4b91729; original global index 5089.
def localCycle00128 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 4256a61c096f1372187526978cf11cfb67b6fa2f52c6b9ada889306ce715fb96; original global index 5110.
def localCycle00129 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.gapUpper 2 2, .triangle 30 1, .triangle 33 0, .triangle 10 0, .triangle 5 1]

-- Original cycle 425bf666b0a175412366aecaa0d556b7eabefdb0dca81870a2e685fa6246ac74; original global index 5113.
def localCycle00130 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 32 0, .triangle 13 0, .triangle 9 1, .triangle 5 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 425cdbac9f3e654768dcb58d01c4303a0774de7f65150dad2ad1f7b06dec6e4a; original global index 5114.
def localCycle00131 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .gapLower 5 2, .gapLower 0 3, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 426de92e63c8ae8f2c90f9072d83a7bb9d53ffdd5e28a47cb1762d8cbc20a088; original global index 5119.
def localCycle00132 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 6, .distance 0 4, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .gapLower 5 3, .gapLower 0 4, .gapLower 0 3, .gapLower 4 1, .triangle 19 1, .gapLower 3 0]

-- Original cycle 42e57fe5a431b2a503a44f28ce592d5042bb19dacc4efd972c8fd3227d6ba9ca; original global index 5151.
def localCycle00133 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 43859528b3ce4e77c188b03564dfe425288f3c7064943b7ded1df80901d82cc3; original global index 5218.
def localCycle00134 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .triangle 24 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 441ad98e65173e2ba9ea8bae06b7f7c79ba1ac91daba9982faf21cd33d448bec; original global index 5272.
def localCycle00135 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 45abd9aa553af55ee7503ac1f1cdcaca741817eb4ed1abf8ec074cc11bed9abd; original global index 5389.
def localCycle00136 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -2, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .gapLower 5 3, .gapLower 0 4, .gapLower 0 3, .triangle 13 1, .triangle 23 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 45c89c9e27960d7d76250a8b38a7d5021a919b0c3a31bc520a4fbd0d4f37e8e6; original global index 5399.
def localCycle00137 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .gapLower 6 3, .corridorLower 5 6]

-- Original cycle 465a8dda17344a8849b33df6f870789231f03c1af282c1d88f27205ef40be7d6; original global index 5442.
def localCycle00138 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, 0, -2, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 11 2, .gapLower 6 2, .triangle 23 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 466e36c7f75e4496b1e9b13f38df4a29c9ff66d3c5527c3025e1b41e2b31706f; original global index 5448.
def localCycle00139 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 2, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 3, .gapUpper 2 6, .thetaLower 2]

-- Original cycle 489a997ef18de4d48479c6948aca18ebc0c662e1902a94f12ad3f562fa39b48c; original global index 5625.
def localCycle00140 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 3 6, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 27 1, .triangle 32 1, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 48ffc50b60592151472df213e021e88905949711176433b59826428768f94a43; original global index 5653.
def localCycle00141 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 2, .gapLower 6 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 498d1596b5b38bb34ff46db3aa4bb39f702bbc6068a9c015da75893ad969fddb; original global index 5704.
def localCycle00142 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 6, .distance 0 4, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -3, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 11 2, .gapLower 0 4, .gapLower 4 2, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 499841d8fd82c62197cdb6c2ce426173d7ddf0d694055504a66ecfb1b0a787f9; original global index 5709.
def localCycle00143 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 3, .triangle 13 1, .gapUpper 4 2]

-- Original cycle 49bf443cead6150e5279513aa363cf1d2455b8d8117e0266c537189f6e702304; original global index 5719.
def localCycle00144 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 1, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 49ca65d814362e6a08a2a08ad4506994c8c78678fb8488b390fe48963f3cb0ce; original global index 5722.
def localCycle00145 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 49dbbee196fd5fbea2a643336befd8ab95087d47380cd136ee04a6c15a6c46a3; original global index 5728.
def localCycle00146 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 2, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 29 0, .triangle 25 1, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 49e7f54a953859dbc7b2528f04fd883a1a1ddbb6598be0246bf4d82acea6a2f9; original global index 5734.
def localCycle00147 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, 0, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle 4a5717c3a324d4fa36cddd6e07f4b5af4d385397876324784128829dea3fefa4; original global index 5767.
def localCycle00148 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 3 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .triangle 11 2, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 4a5b13cde2d032322aa6dd9f37c4250df3822d419f3116d0d82c7d17f645c572; original global index 5768.
def localCycle00149 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 4a7f534b1ee52ce5875366fc235d267552c96cd38fe1013b8d00a5c7d0504cc0; original global index 5778.
def localCycle00150 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 4ac89ddeb1f17182d1e1e3181fbb040d40130cb064c177a511711471d490b809; original global index 5802.
def localCycle00151 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 13 2, .gapLower 6 1, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 4afaf3c67a57a9da04523a8f9728f0320f82742573f4a2704958abb15a50e11a; original global index 5819.
def localCycle00152 : Cycle where
  length := 4
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 5, .distance 0 6, .theta 0]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 3 2, .gapLower 0 4, .corridorLower 0 6]

-- Original cycle 4ba27967b4c57cb7ec9ec6a0ea6baab5b10026e324a717a860f5cf5859ca81c7; original global index 5868.
def localCycle00153 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 2 4]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 5, .gapLower 6 4, .gapLower 6 3, .triangle 29 1]

-- Original cycle 4bc94fb6d4cce39480f526966088e76641a579a7bf3b6541ae02710bf4e46643; original global index 5882.
def localCycle00154 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .gapLower 6 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 4c58ad5b701d07034b66392851eda0bf2621178c5f9c35218044f3381c36a897; original global index 5926.
def localCycle00155 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 4d0b73e7c0a5c08323fc7dc5cb80de3033afd7af4a288d068312cf543e2588db; original global index 5984.
def localCycle00156 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 3 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .triangle 33 1, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 4e2ab306ca8acd803e2f1b0637085d71e6c1cd33629f2059e22d2fe731445e4a; original global index 6067.
def localCycle00157 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 9 0, .triangle 11 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 4e321e5f2d945b5ceefebcb0c26d477badc7f6ce7d9ec243191af9c8e7ddc8f6; original global index 6070.
def localCycle00158 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![-1, 0, 2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.triangle 13 0, .triangle 34 1, .gapUpper 5 2, .gapLower 0 4]

-- Original cycle 4e38ef35c9ecf49f91ea9e35db8d0c5b1858d26d15775d547cc0938a6bd4f7ba; original global index 6073.
def localCycle00159 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 4eaa9b513809b85b94e81d0c68f84e6caaf12587c7f75ce80545b6c1a2ba8d43; original global index 6110.
def localCycle00160 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 4fb6edf5c20d2771e5c0fe364d38c83cce9d0976bdae39be84d58a6110455a75; original global index 6190.
def localCycle00161 : Cycle where
  length := 3
  data := {
    node := ![.theta 5, .distance 5 6, .theta 6, .theta 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 0, .gapLower 6 0, .thetaNext 5]

-- Original cycle 505ef429d3217714150951e3fe985d8c5b8af1f59a6b55a0055b47cb03ecb530; original global index 6237.
def localCycle00162 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, -1, -3, 3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3]

-- Original cycle 50635b019519dcb09d91f06c73530c077c339fe13249549e15d24f72454bbbcb; original global index 6239.
def localCycle00163 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 5073265d8491ceda0b0e647c074b4aadaf7026a0562ba37e942d0aff2fefb8fd; original global index 6248.
def localCycle00164 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .gapLower 6 3, .gapLower 6 2, .triangle 23 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 51fc6f5684ba3f66be26da7c35b062c887bdada5da655a5253a584e36f6c65bd; original global index 6377.
def localCycle00165 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 2, .gapLower 6 4, .triangle 11 2, .triangle 13 1, .triangle 23 2, .gapLower 6 0]

-- Original cycle 5237e0f8539cd5027829a2f6b1d0cb265f9092b5f97b90eb780261ad528f2a60; original global index 6392.
def localCycle00166 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 524be5718e93973de402a669111c62600d194b44ef84bb817ddffa281c6fadc9; original global index 6397.
def localCycle00167 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 0, .gapLower 3 3, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 52ab866aacf7887e45da17144cde3b1fd5cc895ebb61c59e33dbfd44a174f98c; original global index 6425.
def localCycle00168 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 52cc51d86de36dc4d1fe1b4adbd172225e4f5a13208ed9f9714b378e0afc0a89; original global index 6440.
def localCycle00169 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 0 6, .distance 1 6, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .gapLower 6 2, .gapLower 6 1, .triangle 21 1, .gapLower 3 0]

-- Original cycle 52f61300c60a7f201be76cb6376c43b87535c89c0111f2ab5330c0e5e0b94e39; original global index 6457.
def localCycle00170 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 53331295286cc405b93d5d2ebb0138a3a47a5bd3be9ccaa41492126e595e0fc7; original global index 6476.
def localCycle00171 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, 0, 0, -3, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .triangle 11 2, .triangle 13 1, .triangle 23 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 533ea12bbdd91f7b7c05a7a452d4af67a4529ebe422216d110d05d685929eaa3; original global index 6477.
def localCycle00172 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 53a2c3e08345cb799c2d432fd02fbbce13f90d0dbdc046932e4cfea3814ccd80; original global index 6500.
def localCycle00173 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .triangle 11 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 56436e09987eb884487751841a5e0f11b288fed521d4a8255391c682632decd9; original global index 6688.
def localCycle00174 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 18 2, .gapLower 6 0]

-- Original cycle 56e5171a725839ea10453c7937f0754ce3c4a670cef2e49d1c7bc7459866fb59; original global index 6740.
def localCycle00175 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 8 2, .gapLower 6 3, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 572bbc8aa905c9598600466f1a71e986e61f756ce3c4f39031bb3c9f01163fee; original global index 6757.
def localCycle00176 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .triangle 11 2, .gapLower 6 2, .triangle 23 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 589018d3b138bcd926c54cabdf6b9d7e9950def306b207cce474a32a310c4ba0; original global index 6873.
def localCycle00177 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 22 0, .triangle 23 0, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 5983c66b8bb634d0b82e8eb0948e1da3ba8f89dbf273d332e811a8c886f90392; original global index 6955.
def localCycle00178 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 3 5, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 31 2, .gapLower 5 3, .gapLower 0 2, .triangle 5 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 59f03053b9d60a39b7dbb9589d4de7f29e8b05e071bdc304c9d4441db75f2435; original global index 7000.
def localCycle00179 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 5a02f69a215d5bd4c392adfb849fd22987e1a23b75b36f47d0fc72bb9faa7547; original global index 7008.
def localCycle00180 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .theta 0]
    constant := ![2, -1, -1, -1, 3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 6, .triangle 3 0, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0]

-- Original cycle 5a44bf134757bd85e0d0a4f53e2461d511431a13bc7a91aa346f0a99418bfdea; original global index 7023.
def localCycle00181 : Cycle where
  length := 5
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .theta 4, .zero]
    constant := ![0, 2, -2, -2, 0]
    coefficient := ![1, 1, 0, -1, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .gapUpper 4 6, .thetaLower 4]

-- Original cycle 5a50c925c525bb98832856332688267f7c44ea35cd1416d0c6ca65487d6f97b8; original global index 7028.
def localCycle00182 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 8 2, .gapLower 6 2, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 5af98dec2c7fd8ec8a7014c5b1495952d7c537f827358e01040c5dba0115399c; original global index 7079.
def localCycle00183 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 3 6, .distance 1 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 21 2, .gapLower 6 2, .gapUpper 3 2]

-- Original cycle 5b0c55ecb2cf4ef9dfb968b4026b2075a16a0ca291a0d3c9adc7445c86b0a1cd; original global index 7084.
def localCycle00184 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 21 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5bfab694dbd411771dc3b4a8bd85c1d5d2f2609816934efcac9f22e325c5e9d1; original global index 7157.
def localCycle00185 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 5c3ecec023570ace9d4fcd7651d844cef3148c3450d8dbe99a0ceda6460f1154; original global index 7182.
def localCycle00186 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 2, .gapLower 6 2, .triangle 14 1]

-- Original cycle 5cbd6db65416e0d894160359bacc76774c6f6508740565c020ee03e54af987ed; original global index 7215.
def localCycle00187 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 29 0, .triangle 6 2, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 5cd61694f127c91fed896dec404671b9d1eeba015dbeff17de906b69cd8da802; original global index 7225.
def localCycle00188 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5d059d0b4bdde0120ada6cbbf7a32f097750e25b20d68d6a0895ebf4a0bce34b; original global index 7237.
def localCycle00189 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 6, .distance 0 4, .theta 0]
    constant := ![2, -1, -1, -1, 3, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 3 0, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 13 2, .gapLower 0 3, .corridorLower 0 4]

-- Original cycle 5dc8061fc7bfd4befbcb8750e9e7956e98c55283f16b0d3bf87b1b6d2e09c14f; original global index 7294.
def localCycle00190 : Cycle where
  length := 5
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 6, .theta 6]
    constant := ![3, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 0]

-- Original cycle 5de17d299e58a6bd4db63a2ac7a8ff30ed8ae59dbbf6f20c09fcbfa055c744f2; original global index 7302.
def localCycle00191 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 2 6, .distance 2 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 5, .gapLower 6 3, .triangle 27 1]

-- Original cycle 5df4c8c6abb3a5042461d452a2fdbbe5798664111de428039fd94329ce710571; original global index 7308.
def localCycle00192 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 11 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5e30b598f89feede22b7b3bbd14a9b887ce04e2ec406f7f9c01e368d1e7d401f; original global index 7323.
def localCycle00193 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, -2, -2, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .gapLower 0 4, .gapLower 4 2, .triangle 23 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2]

-- Original cycle 5e33fc9de7855f7ff488a2fa445697065abc34af02d65deab064dfdf2a470f27; original global index 7326.
def localCycle00194 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, 0, 0, -2, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .gapLower 6 3, .triangle 13 1, .triangle 23 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 5e42b0beed1ed3167e72358867ea1e802379a3c810de0f2dcdba0af33a404f41; original global index 7331.
def localCycle00195 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -3, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .gapLower 5 3, .gapLower 0 4, .gapLower 4 2, .triangle 23 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 5e893545b2ac81606bd51082d6d16ed49573b4a6b479ef42fc1596999237d85d; original global index 7353.
def localCycle00196 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 0 6, .distance 0 5, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -2, 0, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.gapUpper 2 2, .triangle 8 2, .gapLower 0 4, .triangle 10 1, .gapLower 0 1]

-- Original cycle 5e9e87b64f5e0fcc9321f357d420bddab88bdcb437b8298158e0c7243ab2f1e1; original global index 7359.
def localCycle00197 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 5ec2eab395f17c12ebe1bad3ecc57c8942e3e212fac73ce89b147dc8b759edb6; original global index 7377.
def localCycle00198 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 3 6, .distance 1 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .triangle 21 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 5effac538891b97c478ba5b9a28030b88ad0d0a6f33df06712db6c8ea4a04dc9; original global index 7397.
def localCycle00199 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 1 5, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -2, 0, 0, -1, 0, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true, true, true] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .gapLower 5 2, .triangle 22 1, .triangle 23 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Original cycle 5f5842343f1829d86b05c63844246a8cd381c156717034ce645ad3e2ca13b0a3; original global index 7424.
def localCycle00200 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 1, .gapLower 6 3, .corridorLower 5 6]

-- Original cycle 5fd3cc1c0f3df43cbd6622a5d0da16e30448fb469777d5d1770e482f1961e27c; original global index 7472.
def localCycle00201 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 13 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 60bed6256c79f75d2c3404c8a72dc27ed045ee2b736ce1d429391d8b319f56db; original global index 7534.
def localCycle00202 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 60c6f16653b5134b6b5e8940cd5b6ca4636a23901a7c5b8f15368aeae275fbf4; original global index 7539.
def localCycle00203 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.gapUpper 2 2, .triangle 28 1, .triangle 31 0, .triangle 9 0, .triangle 5 1]

-- Original cycle 62d14abe907e472588db349779d2b474a1bdb885c494d5363623850c83adfdf0; original global index 7712.
def localCycle00204 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 4, .distance 0 6, .distance 1 6, .distance 1 2, .theta 1]
    constant := ![3, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .triangle 12 1, .gapLower 0 3, .triangle 4 1, .triangle 18 1, .corridorLower 1 2]

-- Original cycle 637b38ad4882a5a2f45f6e003e2d9d9034f542740634352d11237b05e27aa138; original global index 7762.
def localCycle00205 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, -1, -1, -2, 2, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 24 0, .gapLower 6 0, .gapLower 6 6, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 6425efe576e28eb9fedfeb07bcb9e47ce06ece7d524221770d01ccd5c51d4443; original global index 7803.
def localCycle00206 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 6, .distance 1 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 4 1, .triangle 23 1, .triangle 22 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 64eb99b3f58d821fb2ef7e837e9da9ca025ece7a08a3bb3148758127bcfb54e5; original global index 7859.
def localCycle00207 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 4, .distance 0 5, .distance 1 5, .theta 1]
    constant := ![3, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 4 2, .gapLower 0 4, .gapLower 0 3, .gapLower 5 2, .corridorLower 1 5]

-- Original cycle 6568d2591a66d29beb88d85605f8311799f34f55e6d406da55ea8dec8de7e208; original global index 7887.
def localCycle00208 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 3 6, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 2 2, .triangle 27 1, .triangle 11 0, .gapLower 0 1]

-- Original cycle 6622f45d5845a97ef0bebeb3a86c124a18b30e3e88ae7df88d99724a953a18f9; original global index 7947.
def localCycle00209 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 3 6, .distance 0 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 29 2, .gapLower 6 3, .triangle 11 2, .triangle 4 1, .gapLower 6 0]

-- Original cycle 671a8b4a25323fc64a1a2a21fdfa40bb20c232869dc482e45da965e5d091010b; original global index 8014.
def localCycle00210 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .corridorLower 3 6]

-- Original cycle 67df4b7c1e52f0fb64bf84e5d3137e3919f8b6e4beb5ee5b0df217d579ae253e; original global index 8075.
def localCycle00211 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 3]
    constant := ![2, 0, -2, 0, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.gapUpper 3 2, .triangle 11 2, .gapLower 0 4, .triangle 12 1, .gapLower 0 2]

-- Original cycle 6837905f812d15c047e199d09522a49aebfb21f5ada3ab0bddf2f6c8deb769d4; original global index 8103.
def localCycle00212 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .triangle 8 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 687476e074250930cf52bb0a1350195dde4b6e397bfc1a3882b7cb99c9a072c7; original global index 8127.
def localCycle00213 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 0 6, .distance 1 6, .distance 1 5, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .gapLower 6 2, .gapLower 6 1, .triangle 24 1, .gapLower 5 0]

-- Original cycle 697b1e9289825839b3a32abbc188417a743fa90e0160e8a8e014de1bd758ceeb; original global index 8205.
def localCycle00214 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 69a8b8dc2fc4104ef4af40ef0f0f379c398fd0eb65952caa542f211644047f81; original global index 8223.
def localCycle00215 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 2 5]
    constant := ![2, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 32 2, .gapLower 6 3, .triangle 30 1]

-- Original cycle 6aa4734ead7f93b75fe1d7ec1a16621eddf7f54096c8d396a8e58e76f4fb14ea; original global index 8304.
def localCycle00216 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 4, .distance 0 6, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .gapLower 4 3, .triangle 13 2, .gapLower 0 2, .triangle 5 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 6acf333a60f4713d289279c176fde67c0e8cc3c850abdd8b6163dfc91cf7a451; original global index 8315.
def localCycle00217 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 4 6, .distance 1 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 23 2, .gapLower 6 1, .gapUpper 4 2]

-- Original cycle 6ad9bdbd7ea4cf485138da4ed2238edfcb1a2fccf9a1b178982e9181a71c8d85; original global index 8319.
def localCycle00218 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 1 4, .theta 4, .theta 3]
    constant := ![3, 0, -2, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 2, .gapLower 6 3, .triangle 11 2, .triangle 13 1, .triangle 12 0, .triangle 22 0, .gapLower 4 0, .thetaNext 3]

-- Original cycle 6bfb4d1814e048dcc13172f5a2afafc9a044fdd0d8afb8e008a6b2c88ce19202; original global index 8416.
def localCycle00219 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5, .zero]
    constant := ![0, 3, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 21 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaLower 5]

-- Original cycle 6d2b75328540d29492e84d94a42173ad3f4b251a4927a379536c493d4fea1e9a; original global index 8491.
def localCycle00220 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 6, .distance 1 6, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .gapLower 5 3, .gapLower 0 4, .gapLower 0 3, .triangle 4 1, .triangle 21 1, .gapLower 3 0]

-- Original cycle 6d667dc7c0d8ea3acbcae303e04879dc51aaabfa8a071f7625bcab5ffc296bbc; original global index 8505.
def localCycle00221 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .gapLower 6 2, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaLower 1]

-- Original cycle 6db31be12453e39649cbb3f63e614363de1b826804234a6831b26d298260e2ce; original global index 8528.
def localCycle00222 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, -1, -3, 3, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2]

-- Original cycle 6e370006e8c88f8d8145cf71ad791e1b9d2b1cc54155cf48cd672bd689d6e4c4; original global index 8555.
def localCycle00223 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -3, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 6e71f76b98c2aaa6bd340a197fec6f8193a25ac998918f5315d6eec4d7929617; original global index 8572.
def localCycle00224 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 6f49f7a84deba72d6b3ba2244c191d4a1c061fb7b252cfd5268781885eb6fb99; original global index 8624.
def localCycle00225 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 8 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 6f52a793329b5c7d120a9795d3572306347b9d2bd5a8b01cee0eb16c26d06d05; original global index 8630.
def localCycle00226 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .gapLower 6 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 6f603bafd1d4de2dee0fdf48ebc13428900c764ee1ed5c5b883ae6c500db5bc5; original global index 8632.
def localCycle00227 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 1 6, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .gapLower 6 2, .triangle 21 1, .gapLower 3 0]

-- Original cycle 6f6a3777c983618bb159f210c8c448251b0788ae4371ee344dbac929701520ac; original global index 8638.
def localCycle00228 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .triangle 11 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 704a3a831f76d1ac8ebce67f01f8ec1dd05b964d391c90ad7b684f253092f158; original global index 8699.
def localCycle00229 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .gapLower 6 3, .triangle 13 1, .triangle 23 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 707937d8cd7c1f82d41f4c2f8ff704be9edc6c224350bb37a9fc8db96c46f206; original global index 8714.
def localCycle00230 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 23 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 71336dace226f43f01607bf54e373e3afa2977f2301be7a0bca5333a441b840a; original global index 8779.
def localCycle00231 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 2, .gapLower 6 4, .triangle 11 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle 715b7e64ca4e7eb5cb6a1de0f09bc1d0c421a7b5d45ba7126d0b827cdccd4f87; original global index 8792.
def localCycle00232 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -2, 0, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, true, true, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 14 2, .gapLower 6 1, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 7239284cf79d63e1bff3e3dc895ba58512444dac8ddccc4765d2f28be983fbe4; original global index 8855.
def localCycle00233 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 2 6, .distance 3 6, .distance 2 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 27 2, .gapLower 6 3, .gapUpper 3 5]

-- Original cycle 72b4769a3659def42408b7d66b846fe6462b7249fc706c96767d2351913d35d5; original global index 8881.
def localCycle00234 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 11 2, .gapLower 6 2, .triangle 23 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 72c01d2f2d0f4aed879a766db22392dfbb839f70f1a74b22433501d73c5d8f5e; original global index 8885.
def localCycle00235 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 72f59c25aeb8ed93b0d30964bba574721cdb748b370b4630717c1874d34aae86; original global index 8907.
def localCycle00236 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .gapLower 6 3, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 7386d928d2bad38085dcd6af5d6893262c6776dc3b11e0ce3beb7a6650a307e6; original global index 8956.
def localCycle00237 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 73b208c4d4df5a50d39aa3f2186774fa2a98cd58d14523455faf3eabd6ea2558; original global index 8970.
def localCycle00238 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 2, .gapLower 6 2, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 73d6eab527c996b2650df1e9bbb2fb4326080d0737507efcf77c75dcea41d07d; original global index 8982.
def localCycle00239 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 7407f547a131912b3351e7094b3c72641d9be3de43611d18c0f4f8d16ee160f2; original global index 9002.
def localCycle00240 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 2 6, .distance 3 6, .distance 2 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 27 2, .gapLower 6 4, .gapUpper 3 4]

-- Original cycle 7463bc0ed66620adb582826fba23c8ff8ca4b98fa77c3f147963223703ed4350; original global index 9023.
def localCycle00241 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 0 6, .distance 1 6, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 4 1, .triangle 21 1, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 74ebb5a6ac75795a5c8cf1b8f55c76aa68e15c775a70b18603d7d838e92cc51a; original global index 9058.
def localCycle00242 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 5 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -2, 0, -2, 0, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true, true, true, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 14 2, .gapLower 6 1, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 755c6b590ebc1fde4d41abec0825adda8283d03813589a1c0c50752d36357953; original global index 9094.
def localCycle00243 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .gapLower 6 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 75b493b9a5a74af80b3a47d225907eb613575c61fcb0c1647eff79c421597f45; original global index 9124.
def localCycle00244 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .zero]
    constant := ![0, 2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 8 2, .triangle 14 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaLower 1]

-- Original cycle 7644e9f5d8395befa07162484c3dc4ddf62681fc2bc53e378928d0dd9d62b167; original global index 9155.
def localCycle00245 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 11 2, .triangle 14 1, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 7653965e15e899a4e2f6e72603a7c9f3bf8e996c76e35a9f7f72fd7bd5ea29cb; original global index 9158.
def localCycle00246 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 31 1, .triangle 9 0, .triangle 5 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 7808c8dd1d18619e9a89b467f63505d896dabfd898ee036574fda80d4023688a; original global index 9280.
def localCycle00247 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 784f20e9ae405caa9a8bf602be45871bde8438b35382adb01aa20f1962215e7b; original global index 9298.
def localCycle00248 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 79bf1f6272e413a4c8c83b1043c845c6809eafbbe7982b5a66c347b332f12e6d; original global index 9418.
def localCycle00249 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 23 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 7a2aa2b0465d2c78c5134e15507d018f890075a6dfd35368dca2e1d604c905da; original global index 9448.
def localCycle00250 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 3 6, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 11 0, .triangle 21 0, .gapLower 3 0]

-- Original cycle 7ba6a86f1cda3e765abe6aacc8b3c4cb481cedf76c0814d00daed7bdc50696a8; original global index 9567.
def localCycle00251 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 2, 0, 0, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .gapLower 6 2, .triangle 4 1, .triangle 23 1, .triangle 22 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle 7bc310ea5c08d61f783e8c6891e4606ed214a242279fc7e17f73f52d40b39a54; original global index 9573.
def localCycle00252 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, 0, -2, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 11 2, .gapLower 6 2, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 7bf6d8d664422f35b64e90fe52003c5e1101a6040b6a0e4049941468e464475d; original global index 9586.
def localCycle00253 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .gapLower 6 4, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 7bffaabb34ab9289046255238b1de7612d58001534dc8a091db9e2135b2aa79b; original global index 9591.
def localCycle00254 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 7d2946e18cb33b7e261a42db69550644d1ff438291c31bf156665bec2af6c663; original global index 9700.
def localCycle00255 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 0 6, .distance 0 5, .distance 0 4]
    constant := ![2, 0, 0, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, true, false] }
  origin := ![.gapUpper 4 2, .triangle 13 2, .triangle 14 1, .gapLower 0 3]

-- Original cycle 7d726b41f13f9e46fe40bbdef9ef053ba98eab82bbc9dd01fb89243a124f22fe; original global index 9726.
def localCycle00256 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 6, .distance 0 4, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![3, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .triangle 14 2, .gapLower 0 3, .gapLower 4 1, .triangle 16 1, .corridorLower 1 2]

-- Original cycle 7d9a5fe4ae9dfa53eb839809fb930eccb36cedcc14d1416db240baa91f22f2b2; original global index 9748.
def localCycle00257 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 7dd18ed04b69d3f5541ac94108b948212d91a5ce5b7ac97f29f31ec44325c9e4; original global index 9770.
def localCycle00258 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 1, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 7e288f5d32c0a54ce241fa1715457a1638716314ce592bcab7958d66e0718e90; original global index 9801.
def localCycle00259 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 4 2, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle 7fb0b2ebe48e428a46f687c2007cbe6d92968f66fe7a5258a876c3bbbbcb2f6a; original global index 9901.
def localCycle00260 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 5, .distance 0 4, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, -1, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 5 2, .gapLower 0 3, .gapLower 4 1, .triangle 19 1, .gapLower 3 0]

-- Original cycle 7fbfdc4a43d215554221c96e4b9ca8ead07a804743d010d5d9b55c67f1deaca2; original global index 9907.
def localCycle00261 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 5, .distance 1 5, .distance 1 2, .theta 1]
    constant := ![3, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 4 2, .gapLower 0 4, .gapLower 5 1, .triangle 17 1, .corridorLower 1 2]

-- Original cycle 800d60fd94cc98cefa80183b7732e15cec49e55d95c47e33c4b00f000b916ab4; original global index 9930.
def localCycle00262 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 21 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 801fa73d78e92194e96e55980c6a3b23568bcc5fa0f5a7536e889f37ca7137d7; original global index 9938.
def localCycle00263 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 2, .triangle 14 2, .gapLower 6 2, .triangle 23 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Original cycle 806567c545730beb8d955366abd7002b33119f8a67ca74e0ca505cd270759545; original global index 9963.
def localCycle00264 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .gapLower 4 3, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 809e9ad6ab26b421f43aadab4b77773087e4bf254bee71ddf7d98fe88a4034de; original global index 9985.
def localCycle00265 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 23 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 80fb0a2a24859ca520d57a74f9a245e2630b61c94093386a384d3fc4e421e1ea; original global index 10010.
def localCycle00266 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 818aed20cabaa910c0e3be014fb6c26b3f474aa787d2dace2983c2cc19f0357d; original global index 10061.
def localCycle00267 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 81ceeb30231f7caf5217c1c48e4d19a7231f26eb7260b17bb24e699e8887fcba; original global index 10074.
def localCycle00268 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .gapLower 5 3, .gapLower 0 4, .gapLower 4 2, .triangle 23 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 82322c0f7de65b4399b6894f8a3a28a855c5ccb10797fcd5fbaeaaaef628adb5; original global index 10112.
def localCycle00269 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 82b2fd0d15fbe55df089f93c2a925dc52a709e11b8ed6b5d47c986a4441f6e65; original global index 10137.
def localCycle00270 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 22 0, .gapLower 1 3, .triangle 21 0, .corridorLower 3 6]

-- Original cycle 83c9183283512b08d3239642e558d28b16369ab35ee13d912423fa99bb1bd1b5; original global index 10228.
def localCycle00271 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .gapLower 5 2, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 8426bcfdd7ba816baa3471f9771ab7c6b49ef8d68a445a80cba4cb5c95d93346; original global index 10259.
def localCycle00272 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 84433a8b176d416133cf6cf9d42f32191eb58c207f91e57b6fb67083b57bc58f; original global index 10271.
def localCycle00273 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 2 6, .distance 3 6, .distance 2 3]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 27 2, .gapLower 6 4, .gapUpper 3 4]

-- Original cycle 8483699b4660f77020c8a36c3c9b5b640d859830eb577f798f1e6b9640ce3b3d; original global index 10288.
def localCycle00274 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.gapUpper 2 2, .triangle 30 1, .triangle 34 0, .triangle 31 0, .triangle 9 0, .triangle 5 1]

-- Original cycle 848ae7f983bfd2b84c683b16a51e36d1546711c23b08f166315be4ffd937ad71; original global index 10292.
def localCycle00275 : Cycle where
  length := 4
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .theta 6]
    constant := ![3, -2, 0, -2]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 18 2, .gapLower 6 0]

-- Original cycle 8497f97a5a233920a382a1bf40da44dae591b26acf48da73ab5955335a2d7615; original global index 10296.
def localCycle00276 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 84b8e4fcfce1e4d158cd1188ea63a01bf3a4e678d16f2ee4979bf7f1c8bd7ae4; original global index 10304.
def localCycle00277 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, 0, -1, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .triangle 11 2, .triangle 14 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle 85411eba28a1c39af979e9e2230b7c9a0bbc300a559399d21ec70a92f8706077; original global index 10337.
def localCycle00278 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 11 2, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 861c39f5f753c58a02b6fb04e02fe9f148d976f5c06929f51b9ea275ab491c77; original global index 10400.
def localCycle00279 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .gapLower 4 3, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 86917d18c63d74768fabea9a7c65b25c2d1712d9dbb29a4b215d670a6fe46740; original global index 10432.
def localCycle00280 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 0 6, .distance 0 5, .distance 0 4]
    constant := ![2, 0, -2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 4 2, .triangle 13 2, .gapLower 0 4, .gapLower 0 3]

-- Original cycle 86b55f4fd3bdbc58a650b7d8cb838fd97ad107e27fafdba57ac1311c271fa05c; original global index 10446.
def localCycle00281 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 8 2, .gapLower 6 1, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 86c71a725212b7ad2a61afab403ffc097a242b59923d27e5b6dfaa6abd213ad9; original global index 10454.
def localCycle00282 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![-3, 0, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 0 5, .gapLower 5 2, .triangle 24 2, .gapUpper 1 5]

-- Original cycle 87af880e1f5bb861156cf384353578b86de0f2f76546e98952bcbd85b58176f3; original global index 10519.
def localCycle00283 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -2, 0, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, true, true, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 13 2, .gapLower 6 1, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 88a836467aeb2c0251dba4e83d5fb4b60ad91d9c49ecb55ac1999163179b3100; original global index 10587.
def localCycle00284 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 2 6, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 89055d5f56a6113fe966dcf56ac18b62c3eb112d04ae4c0bf116052de08e1fd6; original global index 10607.
def localCycle00285 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 8972d65a0b7f97d3a37262028c89114fd547ee1640a275cbb0af5406c44709be; original global index 10638.
def localCycle00286 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 11 2, .gapLower 6 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 89918dad4e22eb38e5fd942e4951c07b111bb7ee6184f5302daa21c1feaa34ed; original global index 10652.
def localCycle00287 : Cycle where
  length := 3
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 6, .theta 0]
    constant := ![2, -2, -1]
    coefficient := ![1, 0, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .corridorLower 0 6]

-- Original cycle 89df97c038abebef38738ec32a5c09908784fabc4216c93d81d9e9f44e25cef9; original global index 10682.
def localCycle00288 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 8bbe63e7e9dff93a21b946d747e83e27bef04adb531de92f6448c63d8c19c702; original global index 10819.
def localCycle00289 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 6, .distance 0 4, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 11 2, .gapLower 0 4, .gapLower 4 2, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 8d32884d6ea40e12e6561dc2f7e58d097217ee4898867a90e73af911337bc59d; original global index 10916.
def localCycle00290 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 8dd957c58cf2a5b7dea6c0fa1cd01e262a70433a8e556776c43fbe5b0c020385; original global index 10979.
def localCycle00291 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 8e4e15239ca4fb3a0b79728d6448b200d194d68177cca691906e3bde1a42c18b; original global index 11018.
def localCycle00292 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 0 6, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -2, 0, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.gapUpper 2 2, .triangle 8 2, .gapLower 0 3, .triangle 9 1, .gapLower 0 1]

-- Original cycle 8eb57df6fc24716e1e457d77acc994455be0d65e184cff610314c3ca1bd77735; original global index 11043.
def localCycle00293 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 4, .distance 0 6, .distance 0 3, .distance 1 3, .theta 1]
    constant := ![3, -2, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .triangle 12 1, .triangle 13 2, .gapLower 0 2, .gapLower 3 1, .corridorLower 1 3]

-- Original cycle 9054b3354095aafd64a78cfa129de079aa71e9caf672c060765d6abfeb40385b; original global index 11175.
def localCycle00294 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 9 0, .triangle 11 0, .triangle 21 0, .gapLower 3 0]

-- Original cycle 9069e5db89dc8ceaeee0b47e28e3a7a4d22db7478e24ba5cef95d8af839e9834; original global index 11180.
def localCycle00295 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 90ae13d66f8abe8a2ae932690ea3186dfcf027aca171da1b47164cdd97416f76; original global index 11205.
def localCycle00296 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 1, .gapLower 6 3, .triangle 13 1, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 9167ebda13077d970793f64db371ff721cb2a24d234d8a30dbbbaeec3e4348c1; original global index 11263.
def localCycle00297 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 10 0, .triangle 5 1, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 91922c1a14513dd612fb50c59d8d5b7c7b9d60ecc7088046140057f2b0f9a0ef; original global index 11278.
def localCycle00298 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 0 6, .distance 1 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -3, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 4 1, .triangle 21 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 919d099d7026aaf28667f74b596815647777812000e2b56481c6e18a61f7a6ef; original global index 11284.
def localCycle00299 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 32 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 919f198c42361f7213547f5db8c2e8b602092a041a9000e3e6333cf2b71564e2; original global index 11285.
def localCycle00300 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 4, .triangle 11 2, .triangle 13 1, .triangle 34 1, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 929f426663e372551ad5e6589d8bbe437a5f865340ee31fbd8d7d8418872cc8e; original global index 11360.
def localCycle00301 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, -1, -3, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 0, .triangle 28 0, .triangle 16 0, .corridorLower 1 2]

-- Original cycle 92ad91e61017f4ad726cf96f0f009018b6866852897306ac750d28f226943cdd; original global index 11364.
def localCycle00302 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 92c9323b8216ee52cf07454cb989ca2a324c03ec11e88e927f8ae47b23738c62; original global index 11375.
def localCycle00303 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 93543a58a811419bc27cf5363af42d34ceda046fb7ac514910e16f8fc896f414; original global index 11424.
def localCycle00304 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 4, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, 0, -3, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .gapLower 4 3, .gapLower 0 3, .triangle 13 1, .triangle 23 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 949c97642fa2d759a2b4747773399aff418abc36e0096d399dc281ec93004ad1; original global index 11531.
def localCycle00305 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 949ffe407a5aaecc6ad091a61b0aa0d45e07dc574f077116d2576305e6054355; original global index 11533.
def localCycle00306 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 3 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 95ef3aaeb29308dc6538f754dd59019e7581a2ac53dc7fa92203b5e0c41bc4c8; original global index 11659.
def localCycle00307 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 2 2, .triangle 13 0, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle 962df4f2f7ec70cea88651299d1c7e271ccc8989b020d025f05662a8db3750e0; original global index 11677.
def localCycle00308 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, 0, -1, -1, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle 966c1b6dc86eeb406cab18a06f62d038f1ef7919a43d1af295ba031787f0452c; original global index 11698.
def localCycle00309 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6, .theta 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -2, 2, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 2, .gapLower 6 0, .gapLower 6 6, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 97755c6177d9206e528efcd2052cf777910164feb32979306cd4dea2ae91a96a; original global index 11768.
def localCycle00310 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 4, .distance 1 4, .theta 1]
    constant := ![3, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .gapLower 0 4, .gapLower 4 2, .corridorLower 1 4]

-- Original cycle 9785986cb26439053667f11c8d7dcb9bd3f3f39a181048788ce480e325234af7; original global index 11772.
def localCycle00311 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 0 6, .distance 1 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, 0, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 8 2, .gapLower 6 3, .triangle 21 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 97d62c796fa02017a0cbb1314964260f5533e63bd54fb314dfaa70200779beed; original global index 11792.
def localCycle00312 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, -2, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .triangle 12 1, .triangle 13 0, .triangle 23 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2]

-- Original cycle 982e886df5c3ec4a2f2284a167f816180587478cb4ddb7dd05c76f653ae9d0d1; original global index 11821.
def localCycle00313 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .gapLower 0 3, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 990b285c6dda0ca845923269d9c033a24f792b7b57470e5bbe9e4d615a081ccb; original global index 11883.
def localCycle00314 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 6, .distance 1 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 2, .gapLower 6 3, .gapLower 6 2, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 99415703021fc8c30cd6545adc2183eca16c242438e883b179808e058afdbc7e; original global index 11901.
def localCycle00315 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![-2, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false] }
  origin := ![.gapLower 0 3, .triangle 13 1, .triangle 34 1, .gapUpper 5 2, .gapLower 0 4]

-- Original cycle 99f4d6b13c1c5c464270d5808d97f6b2fbc2bf7bc2dcdaff478ecef7b3e4c434; original global index 11953.
def localCycle00316 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 9a2f99326a854ea852f65deba511adb7a0c5b50e390e853e177e7826f7398e12; original global index 11977.
def localCycle00317 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .theta 3]
    constant := ![3, 0, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .gapLower 6 3, .triangle 24 0, .triangle 20 1, .gapLower 3 0]

-- Original cycle 9ab101ecb0155443db42908a20a0b708f26cdcff4326c9354fcf3d21f8dad6da; original global index 12021.
def localCycle00318 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 5, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 2, .triangle 14 0, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 9aec18adc044062d72c0e113f3294a8c4dceafdeb198410223c8b78ff6b56eb4; original global index 12041.
def localCycle00319 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 2 3]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 2 4, .gapUpper 4 5, .gapLower 6 4, .triangle 27 0]

-- Original cycle 9cdee07bfad5d0c7a5ceed01dbbba885d482e93dfba6541b1123878a714b7641; original global index 12202.
def localCycle00320 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 9d04ad2b37561ca294af4fc302dbdc77465d915d7f46306d5f277d113e0a56d0; original global index 12213.
def localCycle00321 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 2 6, .distance 2 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 5, .gapLower 6 4, .triangle 29 1]

-- Original cycle 9d9d0295466fc4bd13568c9c9384e92bcc1f9a6d0d0dcc59d50945ffbb772a45; original global index 12255.
def localCycle00322 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 8 2, .gapLower 6 1, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 9db1e43273ec8d51937b6675ff5b4d18fbd494bd0d8a5f50fe74595133d42211; original global index 12269.
def localCycle00323 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 4, .distance 0 6, .distance 0 3, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .gapLower 4 3, .gapLower 0 3, .gapLower 0 2, .gapLower 3 1, .gapLower 3 0]

-- Original cycle 9dccc4f771008661f5b9d5f75a159e4ddfeee4c770ce31ba2ff99072db412e06; original global index 12277.
def localCycle00324 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 2 3]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 2 3, .gapUpper 4 4, .gapLower 6 5, .triangle 27 0]

-- Original cycle 9e5a7c0d8d4c2f95d5a8a3614e0ee7d82a4a2a93df83771d2d71d2daccec6e74; original global index 12329.
def localCycle00325 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 32 0, .triangle 13 0, .triangle 6 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 9f402d27f2a23a8c3ee0f36bc0258b452159cbe0b5ce5f2535b348c1c6fd36bc; original global index 12396.
def localCycle00326 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 11 2, .gapLower 6 2, .triangle 24 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 9fbbce0c68a2e514e6295b5437c9b1113de9171a5e199e43326c005ecb30dd87; original global index 12432.
def localCycle00327 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 0 5, .triangle 14 0, .triangle 24 2, .gapUpper 1 5]

-- Original cycle a053f2d5b6c282a8ff8986d1179f96779d887c8c2b5a5a086d04810072e9a40f; original global index 12476.
def localCycle00328 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle a0b483040cbcc6ac9c967c77aaf672e98034c4f6c4fe2ef7b6ffccad4ae42c5c; original global index 12502.
def localCycle00329 : Cycle where
  length := 4
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 6, .distance 0 4, .theta 0]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 4 2, .gapLower 0 4, .corridorLower 0 4]

-- Original cycle a1c056ad4c1f877c0fe37e092ce08be33bfb4981207b90d15ddceafff414ecff; original global index 12582.
def localCycle00330 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 5 6]

-- Original cycle a27450e7868288bcfbac40945b76a31ea294986c0ea360286e8844cb31589428; original global index 12638.
def localCycle00331 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![2, 0, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true] }
  origin := ![.gapUpper 2 2, .triangle 30 1, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 12 0, .triangle 6 1]

-- Original cycle a2bd3034706dbbb1baee5e48d755c734d39975b18990d9a0a9d5116a428644b4; original global index 12653.
def localCycle00332 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 1, .corridorLower 1 6, .thetaLower 1]

-- Original cycle a2e5d4bf4cb84d0da3bc18c6b7027ee576232ccc5483d89c7e4a49d51d570b52; original global index 12670.
def localCycle00333 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .theta 0]
    constant := ![2, -2, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaNext 0]

-- Original cycle a2f39a4bc45e6f560600d6159022dfea9c09c9fc8c8dfc50eb1035f219909f18; original global index 12673.
def localCycle00334 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle a305a43d71267c3bd3eb3be0bb2492805d3724402644a0d9f8ced62490af8753; original global index 12677.
def localCycle00335 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 0 6, .distance 1 6, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 8 2, .gapLower 6 3, .triangle 21 1, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle a30d0dff7defd28d78dc8f9596ea3d6dc1e2e9d9fdfce588694e29ceedc44aed; original global index 12678.
def localCycle00336 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![4, 0, -1, -1, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .gapLower 5 5, .triangle 26 0, .triangle 27 0, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle a394b63f95e949f6b0a5b8ee9731fc31638d457e875177aee01f607694f4bb99; original global index 12713.
def localCycle00337 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 29 0, .triangle 6 2, .triangle 12 0, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle a4a946166923d1fc75457103dfd6b535bb2afe9d2ad209d353bc2d3dab6f22d9; original global index 12797.
def localCycle00338 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 2, .theta 0, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -2, 2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 32 0, .triangle 13 0, .triangle 6 1, .gapLower 0 0, .gapLower 0 6, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaLower 1]

-- Original cycle a4da85c34fe6a88de8789b7dea4f2a46d8e3ea609dbf01e34e6ecec291cf00b1; original global index 12811.
def localCycle00339 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 32 0, .triangle 13 0, .gapLower 0 2, .triangle 5 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle a5713d4b6d7fcbae861e4527cba6d22af813c97e80633193aefe57cfab9b4122; original global index 12854.
def localCycle00340 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle a5d1b83ac444697d349fa07c6b1ce16bac05a3f555bf2878d8693689cc644e91; original global index 12881.
def localCycle00341 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 4, .distance 0 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .gapLower 4 3, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle a5e5d3c2c0218692e5b65635dbb25a117266e48e52f9bf85d13fe6368623505e; original global index 12887.
def localCycle00342 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle a5eb484e872dd5101fc86918998302b0dce0b05d081b95423fa54808df18bf49; original global index 12892.
def localCycle00343 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 5, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .theta 0]
    constant := ![2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 12 1, .triangle 13 0, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0]

-- Original cycle a5f53241385db566e6ac7d8d22e9273dbcfbb880fc54f400699aaddc89edd3fb; original global index 12896.
def localCycle00344 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 11 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle a6f2e43be5301f7c353ceed3ac409531089ce3951dd1dc7b51d444d1996fc6db; original global index 12972.
def localCycle00345 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .triangle 14 1, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle a761f6d7e0662ccc5d19c332394b913137771b521da4ce5649db9a88b682e941; original global index 13022.
def localCycle00346 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![4, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 11 0, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle a7624ac8b59be406bdd33042142dfa059a463c3ff692b10a62b1ac5f7427082f; original global index 13023.
def localCycle00347 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 31 1, .triangle 9 0, .triangle 5 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle a7883f523cc6ad999ef9260403e0d313e717cfa358a765cec8dbc4fc1c69367d; original global index 13033.
def localCycle00348 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 10 2, .gapLower 0 3, .triangle 9 1, .triangle 5 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle a7cc3f3300ee336c36f29e07214b78c70eb6ac60bec48131fca739b7a9a64bc7; original global index 13056.
def localCycle00349 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 6, .distance 1 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![4, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 11 2, .gapLower 6 3, .triangle 21 1, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle a7d24fd7df35e7b64c1165cf52c2d5c1033f539d557999be82dab59b98850785; original global index 13061.
def localCycle00350 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 14 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle a7d2548053c3ad2f27ddf1f8e07beeca6d7ae49861787bdb00ac19414601ae34; original global index 13062.
def localCycle00351 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 3 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, 0, -2, -2, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 11 2, .triangle 13 1, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle a80c1a6d2ff687b250e90d9df29c04ef0056314532d51df9b5600e1641fd91e7; original global index 13083.
def localCycle00352 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 11 2, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle a91f0d79972e925b1e89ab560a51ac59bd2f1f6914927e2e528d10258ef8611a; original global index 13166.
def localCycle00353 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .gapLower 3 3, .triangle 9 0, .triangle 5 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle a9eec3236ec7e7ecd2d0e9b37749282df18288128529e550cc2e5597ef785caa; original global index 13229.
def localCycle00354 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 0 6, .distance 1 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![4, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 4 1, .triangle 21 1, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle aa0a1c4f350f1828c423c5b632f15fe569eccef58d5b8469392b34d09dddf72c; original global index 13236.
def localCycle00355 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle aa445ec2205102d5cae6cab86ec68c0bba35a2e4efa0ab03bbfb61d0b151613b; original global index 13257.
def localCycle00356 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 12 2, .triangle 14 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle aabfa58ac4de8f93ac833e1e7f82226b9f39a3bd40ca880acaa2178dd930fa72; original global index 13304.
def localCycle00357 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 4, .distance 0 5, .distance 1 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .gapLower 4 3, .gapLower 0 3, .gapLower 5 2, .triangle 22 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle ab30e26e1f51eb27efd2bd77e7ec4e904d2ea947021f1586f6917cc6488b31ac; original global index 13335.
def localCycle00358 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 1 5, .distance 0 1]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 3 1, .gapUpper 1 5]

-- Original cycle abe578e19f7a128035f9cecf77a5799e1fad36bbf9d2871af035e7fea077463d; original global index 13387.
def localCycle00359 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 3 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 27 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle ac3dde7e6a8b17485c19c8b3458424b96cc6ac4595f838ba1d683e7b56f79875; original global index 13428.
def localCycle00360 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 0, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle acc450c2a10d46499f35dbd665aa5c28b18702ff6a8eebf46bcc0c6ad5ae959e; original global index 13467.
def localCycle00361 : Cycle where
  length := 5
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 3 6, .distance 1 6, .theta 6]
    constant := ![3, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 2, .gapLower 6 4, .triangle 21 2, .gapLower 6 0]

-- Original cycle ad1a9be686b0edb3fb029cf661c66aa8368ccc9b45415078f8d38b3ef152af1f; original global index 13493.
def localCycle00362 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 0 6, .distance 1 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 4 1, .triangle 21 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle ae0d3e85487a3700c2f89194323281ab4f27357163cd310e32a75bdaf2626b95; original global index 13581.
def localCycle00363 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle ae69ec5563c9fdd24271b1a69c056dc3c97bdd9136ed6dd384d15b5e9dc91020; original global index 13612.
def localCycle00364 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 0 6, .distance 1 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 8 2, .gapLower 6 3, .triangle 21 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle af0d6e9717ad64d30d3c037f28f7017d827030706c2e7ec10522896a9d2196ca; original global index 13666.
def localCycle00365 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .gapLower 6 2, .triangle 4 1, .gapLower 6 0]

-- Original cycle af94d88b60d6c4997b3907c7a1769c92b77cc0dbbfea8dfa2a0d815a960c6f35; original global index 13715.
def localCycle00366 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle b14a9c705338cc73e6d9d1234ea47b929a9acfb8ab14ccdc141056acee381215; original global index 13850.
def localCycle00367 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle b15e4c5d721afc9ab8d6313f88ecf7d1f38c5f10e933ee8f319aeb9854ff610f; original global index 13856.
def localCycle00368 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle b15f2d2f657393faf4e3659fcd6f94db6f9005a1e788e2e739cc50069daff8bb; original global index 13857.
def localCycle00369 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, 0, -3, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 11 2, .gapLower 6 2, .triangle 23 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle b17da3448a1e12a8eed0cd0b17b4038ffcce1d6db3e65cf8eb0c13906cec00b4; original global index 13873.
def localCycle00370 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .triangle 24 0, .triangle 20 1, .gapLower 3 0]

-- Original cycle b2303bacc672a8f7c199df375166841753f00fb80e443472174ef31b0958e5c6; original global index 13923.
def localCycle00371 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle b23206c55d7c2404769839f8fe45f32a8b9c874bd4d4918c054809d33ea1e603; original global index 13924.
def localCycle00372 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 18 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle b2972c62279d79000da1604ea9e3bfd9f4272af61190db52cacd52cde6c3c341; original global index 13960.
def localCycle00373 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, -2, 0, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 8 2, .triangle 13 1, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle b2e1d91abe38ac003ef2faf9c0c2f52a273e205fe0c67e8e855c41848a5db3d2; original global index 13982.
def localCycle00374 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 4, .distance 0 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .gapLower 4 3, .gapLower 0 3, .triangle 8 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle b32b03d09095687ab482069cb332146b8f67c22aa8d3fdeaabf908572a16ad11; original global index 14001.
def localCycle00375 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle b3b93c0e5cd56be94051366d7d5a3cf71d273f7bf3a0cb215ed55d3f65fe9cd4; original global index 14037.
def localCycle00376 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle b3fc8a59439ad918d27e1723c487f0af993bae50978782fd04b19a02d5fada11; original global index 14056.
def localCycle00377 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 3 2, .triangle 14 0, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle b4f169115e5465d48cbbac7952aa480a27b9f6d9b544c08f3f4793e6ef47ccef; original global index 14133.
def localCycle00378 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 3 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, 0, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, true, true, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 11 2, .gapLower 6 1, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle b5337716f14445e9b09a7603bb119b775cbcf567329f95f8f024124eaf41e52f; original global index 14158.
def localCycle00379 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 5, .distance 0 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 2, .triangle 14 2, .gapLower 6 2, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle b5762297bd90645e676e8b3637f046ebd029c36e501b2bff13cc1079b054e833; original global index 14180.
def localCycle00380 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 3 6, .distance 1 3]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 21 2, .gapLower 6 2, .gapUpper 3 2]

-- Original cycle b5ce4a6cf18a2946974b6421d593c7293217f87e34188b74f1a15496901b7f9c; original global index 14204.
def localCycle00381 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, -2, -2, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .gapLower 0 4, .triangle 4 1, .triangle 23 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Original cycle b5d17de016fbb58bd2af01eeb9e78c83d85b7927b0d3bf1f8fe73852a28b44f1; original global index 14206.
def localCycle00382 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -2, 0, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .gapLower 6 2, .triangle 13 1, .gapLower 4 2, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle b6a237ff7ccc12fb1b0faa5dfc3be2eee4130d7f698ffe450a400a1f95555a04; original global index 14274.
def localCycle00383 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 4, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle b7aaa0543b1a33948feba696feb6f2ed42a8c3b39087538dee57c2153b79a0c0; original global index 14328.
def localCycle00384 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 5, .distance 0 4, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, -1, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 5 2, .gapLower 0 3, .gapLower 4 1, .triangle 19 1, .gapLower 3 0]

-- Original cycle b8168c5549051cc4d62dcc3073b391dcdc4da49a127c1ba85b74548a3144b8ca; original global index 14361.
def localCycle00385 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle b8625f526fe17e3b2726fb6a82a9633ce435d3278d793adb0507a05d16dcb86f; original global index 14388.
def localCycle00386 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 11 2, .gapLower 6 2, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaLower 1]

-- Original cycle b8843a7f0c257ba5925d2252dc68d2c0400954280ce5659c11b2a72c21889d92; original global index 14398.
def localCycle00387 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .gapLower 6 3, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Original cycle b95ecb5e3d9f7c923e8f0a988d664dacfc79fdc5e110f0e54252acd2c03bce79; original global index 14464.
def localCycle00388 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 2 6, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 30 1]

-- Original cycle ba6af48a4380f505c67fca5b574ebfee59fe96c9d93656155599c1b973ff9cdf; original global index 14557.
def localCycle00389 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 5 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 14 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle baa01273e0e4397e4b728a2d7e3bf5c07c612ab9e52a34f4bf820e840b8f1cfd; original global index 14572.
def localCycle00390 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 5, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 4, .theta 0]
    constant := ![2, -2, 0, -1, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .gapLower 5 2, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 13 0, .corridorLower 0 4]

-- Original cycle bab3e220506ac29379b84b4491a3495adcd02e0f68cd73d1bcd7fb5faca8f05b; original global index 14583.
def localCycle00391 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 3 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 29 2, .gapLower 6 3, .triangle 21 2, .gapLower 6 0]

-- Original cycle bad6d792bbfd431ba1071e8a76dac2cf34565f8b164aac358f55b4179bdfbe84; original global index 14594.
def localCycle00392 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 2 4]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 2 3, .gapUpper 5 5, .gapLower 6 5, .triangle 29 0]

-- Original cycle bd13cb54e0e3bcbfb87a9450906f9ff0cf01d5ccd479744c2c072c6f4fd62a14; original global index 14752.
def localCycle00393 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle be3c114b5ee5832c1de80f0f16bbfd5964c8f6c04a6e944e46dc7fbea2d89bc3; original global index 14837.
def localCycle00394 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 5 6, .theta 5, .zero]
    constant := ![0, 2, 0, -1, -1, -1, 0, -1, 3, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 6 1, .corridorLower 5 6, .thetaLower 5]

-- Original cycle bf73c43910fe13c49cd850955700c3e47903a5a3d7a359f64db6958dfd15b8f8; original global index 14937.
def localCycle00395 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .gapLower 0 3, .triangle 6 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle c03c06f106ab7558003249538f7c5211d73985010a6a0c7205d57237994cb2a3; original global index 15009.
def localCycle00396 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle c15287a057aee779a86db0831bd7263004b0b9535f1497d3b99d56c53416e1c8; original global index 15093.
def localCycle00397 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle c1fc63d420509bbd9fbf6c79a80806ecae2f15d1144150ed4be59f1a68404703; original global index 15146.
def localCycle00398 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 22 2, .triangle 24 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle c3906b9f401f3d6868243908e8d57c95f483875224f4311e8faf5417dfea2413; original global index 15261.
def localCycle00399 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 6, .distance 0 5, .distance 1 5, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, 0, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 11 2, .gapLower 0 4, .gapLower 5 1, .triangle 20 1, .gapLower 3 0]

-- Original cycle c412980b25f8f90cd68b1a0b0c334965a6be1ac5fd5a1e463ba98434678d8b3f; original global index 15293.
def localCycle00400 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -1, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 2 2, .gapLower 5 4, .triangle 10 0, .gapLower 0 1]

-- Original cycle c5101da9b20e0f261afbfeb22af1eca859b3b1ad88075e956ced4ac29a9822c3; original global index 15376.
def localCycle00401 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 2 3]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 2 3, .gapUpper 4 4, .gapLower 6 5, .triangle 27 0]

-- Original cycle c54f26bb88ff63d6bc503546de9a448f1ac641c1cbe2eefc6b924b9a0da8019e; original global index 15394.
def localCycle00402 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 0 6, .distance 1 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 4 1, .gapLower 6 2, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle c63f6f2c1ab9dd153c82553524990e5ee9819a9a5eb2dfc924f19d5d9c799a07; original global index 15459.
def localCycle00403 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .gapLower 6 2, .gapLower 6 1, .corridorLower 1 6, .thetaLower 1]

-- Original cycle c65021b0abedf3059a0a46533b3e931758878b1f139ba087bd3e1861d85888da; original global index 15467.
def localCycle00404 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, 0, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .gapLower 6 3, .triangle 23 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle c74fc1c753b2ac5c45213976408f6430eef09811f7e45e78f330b0c2123858a0; original global index 15553.
def localCycle00405 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 3 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, 0, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, true, true, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .triangle 11 2, .gapLower 6 1, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle c79946d59c4dc9c59fce54cc462442c56d3d8d045b06fc8924158f1102f94870; original global index 15578.
def localCycle00406 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 2 6, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 11 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle c8507f34c5cfcfb847853cb0bd65aaa3119cab3a9c5279b37eeadf121f29b8c7; original global index 15635.
def localCycle00407 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 5, .distance 0 4, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .theta 0]
    constant := ![2, 0, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.gapLower 0 6, .triangle 3 2, .triangle 12 1, .gapLower 0 3, .triangle 13 1, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0]

-- Original cycle c851d78bed9f0b93313f04735c1a4a6621e06f7e7910683d8fb29461190eff17; original global index 15636.
def localCycle00408 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 14 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle c96f5e1056774a31be68084dab072254750f7b1f038ef7e8a7825a648a19f27a; original global index 15747.
def localCycle00409 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle c9ae2fca1e99071a83bf099277049c20c644a011901ddfb7a4220fb907699afc; original global index 15767.
def localCycle00410 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle c9d2f6806e50ba59762c1c9e99d60010adebd68e4f9a52c5c57b3d8aa5531a95; original global index 15775.
def localCycle00411 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -3, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .gapLower 6 3, .triangle 13 1, .triangle 23 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle ca5178bcbc5d55f9b39dd0a3d7188bbb984974acde9ec860ef77436ba26fc0d5; original global index 15814.
def localCycle00412 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 3 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 1, .gapLower 6 3, .corridorLower 0 6, .thetaLower 0]

-- Original cycle ca8a061bbed47eb5c653e74878c9b7064402c1f33f335bb5d3e4fc127689a276; original global index 15829.
def localCycle00413 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 1, .gapUpper 5 1]

-- Original cycle cb42e35031f6c03149a9245f16d55f5aa70894a96381429b5372577d9b90a5f6; original global index 15876.
def localCycle00414 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .gapLower 2 3, .triangle 6 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle cb5a6b7e7ebb9443a48fe6b01e4f4494ab7748443bd1d7c74506363f109642ed; original global index 15886.
def localCycle00415 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 5, .distance 1 5, .distance 1 4, .distance 4 6, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .gapLower 5 2, .triangle 22 1, .triangle 23 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle cb6d52de8d8700f542c0e3140b9e2ed77f25ce99b562d4043831bb5029cb6165; original global index 15892.
def localCycle00416 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .triangle 11 2, .triangle 14 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle cbc661c5d7b71dc234c7471b5c37ec11acc650c653edab86d86bb9cdd699a57a; original global index 15923.
def localCycle00417 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle cca01396c556cbe8bcb03beb1d8b131213c9960d8875b6c1099ce951a27a00cd; original global index 15992.
def localCycle00418 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 0 6, .distance 1 6, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 8 2, .triangle 4 1, .gapLower 6 2, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle cca95fd85a6527d3c4562bf0cf82bf46496cae0553c0d04c45c2f430a8e63008; original global index 15998.
def localCycle00419 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 23 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle cd8a14195a9389477f8742b809c3e606919c2ff60ea148f063eae69ac7a9279f; original global index 16061.
def localCycle00420 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 2 6, .distance 3 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 11 2, .triangle 4 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle cde349ea575e611f737768da4e21d14883f2d7b197449224741c41e255c92c76; original global index 16078.
def localCycle00421 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 31 1, .gapLower 4 2, .gapLower 0 2, .triangle 5 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle cdec70a0276a6fe9a7b306dca89e4a2e2776c0be8eb5080f406b7c88813dab6f; original global index 16083.
def localCycle00422 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 29 2, .triangle 8 2, .gapLower 6 1, .gapLower 6 0]

-- Original cycle ce18cb1bb50049b7c9970a78b88d0f3d7af3df8337395c4320c468018a4e96b2; original global index 16102.
def localCycle00423 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 8 2, .triangle 4 1, .gapLower 6 0]

-- Original cycle ce938c55adebddcb03c92dcd3533ec92192a827ccc8db1126d7c76bb15885dac; original global index 16133.
def localCycle00424 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 5 6]

-- Original cycle cf270693f494a9815e3e12157a91b380b0906960af415dc40955d9ba3f10c71c; original global index 16165.
def localCycle00425 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .triangle 9 0, .triangle 5 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle cf900c8c29c76f8201003d5609ca0e4466542d4a3a70369423bef891c75aa88e; original global index 16193.
def localCycle00426 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 0 6, .distance 0 4, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 32 0, .triangle 13 2, .gapLower 0 3, .gapLower 4 1, .triangle 19 1, .gapLower 3 0]

-- Original cycle cfc8b096c4ff6fa55f876dd8a1cf43a7c3cac1e5311cdcd2ba27acf8f6afd8a5; original global index 16214.
def localCycle00427 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle cfda8c25794a795693772daffb38f296d8a82522e1db476442f48b7b91361092; original global index 16220.
def localCycle00428 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .zero]
    constant := ![0, 3, -1, 0, 0, -3, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 11 2, .gapLower 6 2, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaLower 1]

-- Original cycle cff23b3ea7bcc3cabd4bbebdacc5e6556941799c45b3369c6faf4d4c6ae89ee0; original global index 16229.
def localCycle00429 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 2 6, .distance 3 6, .distance 2 3]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 27 2, .gapLower 6 3, .gapUpper 3 5]

-- Original cycle d0707f29f5699c38e5f68713c6673050ff6e179b156f69901eb4641388c039d6; original global index 16270.
def localCycle00430 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle d185796515653c39c9bd4b1dac4f47ef42a0781253e68aab1eb7abb7910d8984; original global index 16352.
def localCycle00431 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 9 0, .triangle 5 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle d250cd2d709983bbeaf63198f7afc1d0fd32a5aef248d16b21d9efe132d445f1; original global index 16406.
def localCycle00432 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6]

-- Original cycle d28b3cb298fec238c2afa66e8a44cdddd1546cd0198f232da6d777023b7fb9f6; original global index 16430.
def localCycle00433 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 6, .distance 0 5, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 32 0, .triangle 34 1, .triangle 14 2, .gapLower 0 4, .triangle 7 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle d3233f36200084f06501361f0a12b301c28bf6ae7da476f3cc83e38fc64d711c; original global index 16469.
def localCycle00434 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -1, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle d3a5da679f14bb37da2217a874478ac579b09633e5ac97141cb3d672abf06185; original global index 16512.
def localCycle00435 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, 0, -3, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .gapLower 6 2, .triangle 4 1, .triangle 23 1, .triangle 22 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle d3c82f36810ee91a599755bf6f3fa71d4e4e1275498fb89f615a645a6d1fb7ab; original global index 16526.
def localCycle00436 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4, .theta 3]
    constant := ![3, -1, 0, -3, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 1 3, .gapLower 4 0, .thetaNext 3]

-- Original cycle d3f0ab1cc517680327776045ea4b90fc8785d2bf73813029bd9d4b5ae8cfb6ca; original global index 16542.
def localCycle00437 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 0 5, .distance 0 3]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 3 2, .gapLower 5 3, .gapLower 0 2]

-- Original cycle d4c684ab2ef6b870a17600a5d65fa8472c1ab7e15d542baee740760875d20237; original global index 16599.
def localCycle00438 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 2, .triangle 12 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle d51252569d99a45e11db9572037453a558881cf3e59ff046d8a4297a47ef4e89; original global index 16626.
def localCycle00439 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .triangle 14 1, .triangle 24 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle d514ea78caa13f27df55697a6423df6e3755a2d66d3d6d97b7d4dc7dea2c439c; original global index 16628.
def localCycle00440 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 3 2, .gapLower 4 2, .gapLower 0 2]

-- Original cycle d5a39a1dee5a34b0466d7b8fb49993b7614d94c344d3fc8d08c8a57e4239c62e; original global index 16676.
def localCycle00441 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -3, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .gapLower 6 2, .triangle 13 1, .gapLower 4 2, .triangle 22 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle d63136411f296de940001120088718b85ae3d0bde83d77313e44cff2cf23eceb; original global index 16720.
def localCycle00442 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 29 2, .gapLower 6 3, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle d634e027126a47db6c13c3d12403ef02e4220e5d509fd75cc6b45e5292ff3386; original global index 16722.
def localCycle00443 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 5, .distance 0 4, .distance 1 4, .theta 1]
    constant := ![3, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .triangle 14 1, .gapLower 0 3, .gapLower 4 1, .corridorLower 1 4]

-- Original cycle d6e3260d0a078c3ac094845698aa8d932b4bd53e925890257882357f1671f74b; original global index 16776.
def localCycle00444 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle d73e5ec5d1d160eff8e6fb4c110a687f39270640953a424fb1656df0807fd6b5; original global index 16798.
def localCycle00445 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 0 6, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 2 2, .triangle 8 2, .gapLower 0 2, .gapLower 0 1]

-- Original cycle d79a12b9fb1cb90f5cbbf194602f124131e6671fc70ed749f4dc2daf78588afe; original global index 16824.
def localCycle00446 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 2 5]
    constant := ![2, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 27 2, .triangle 30 1]

-- Original cycle d81df5cbc1cf9241d36bad843ddbc094d0476ec3759fc9e9ddc7a44112c4ffcc; original global index 16869.
def localCycle00447 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 4 1, .gapUpper 1 5]

-- Original cycle d8554c21cad7cfb4ababe4226108ec386f9f9fca36b827e2dc5f1293f9300978; original global index 16885.
def localCycle00448 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 4 6, .theta 4, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 18 2, .gapLower 6 1, .corridorLower 4 6, .thetaLower 4]

-- Original cycle d8643ee193e908a6f68aae8870709c32defeeeac306e83e1f91053f805eb6fb1; original global index 16892.
def localCycle00449 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, true, true, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 14 2, .gapLower 6 1, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle d8964c85a240dcb252ba945ede390c6b5337da43ab248cada6cfde8576a21f81; original global index 16904.
def localCycle00450 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle d9c9c36bbbccee3fb6eb56f6922a2a1cc871d84746f1b8c441da5644aee17864; original global index 17016.
def localCycle00451 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .gapLower 6 3, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle da04eff3d0971e218bda9302f9700de5225c3d399ad79b90ba9a3bb3fdd2e07b; original global index 17036.
def localCycle00452 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 1 6, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .gapLower 6 3, .triangle 4 1, .triangle 21 1, .gapLower 3 0]

-- Original cycle da21d69c15586159c17c752da1dceec45bafa09a710a7311fddffa8acb020f5f; original global index 17044.
def localCycle00453 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 10 2, .gapLower 0 3, .triangle 6 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle db2faa6ba162b6ccbfb2493637f88efcaf45809b5a5b99985d0aa818a94377ea; original global index 17130.
def localCycle00454 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 3 6, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 3, .triangle 32 1, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle dc04151c255f5e963a12de3afbf5188f325eebb29798c219fdea9b7ab1e4e796; original global index 17198.
def localCycle00455 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 4, .triangle 14 1, .gapUpper 5 2]

-- Original cycle dc71ad886bb99e53346125279377e71c2eaa9d4e4332adb9eb04951f34594b58; original global index 17227.
def localCycle00456 : Cycle where
  length := 4
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 6, .distance 0 5, .theta 0]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 4 2, .gapLower 0 4, .corridorLower 0 5]

-- Original cycle dccf3ad7b3ec20b4c0202af4d5154177c8b4a698d103ac89ac11404af0ac2789; original global index 17256.
def localCycle00457 : Cycle where
  length := 5
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 8 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle dcf07fea1327f406ab61ae53a578600e2ba28aa08086a672e21fb5d73c329c9d; original global index 17268.
def localCycle00458 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 5, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .theta 0]
    constant := ![2, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true] }
  origin := ![.gapLower 0 6, .triangle 3 2, .triangle 12 1, .triangle 13 0, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0]

-- Original cycle dcf254fead4f5e4547a2c9f1b6f27c8e1c0fb787795728c9baf2a3e362fc2a6f; original global index 17272.
def localCycle00459 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle dd0c9b63a447098b2b737551bb1c3470c16e0a8dccfdad8d7bbea21419728c70; original global index 17280.
def localCycle00460 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 0 5, .distance 0 3]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 3 2, .gapLower 5 3, .gapLower 0 2]

-- Original cycle dd39a401c84be899299b3c141d74149735415e758285e9a33e2596105eae6490; original global index 17299.
def localCycle00461 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 2 2, .gapLower 4 3, .triangle 9 0, .gapLower 0 1]

-- Original cycle de05c921e8479d8e3d5516ae3a2072cb72c56ea59691164f9411a5696121f7a3; original global index 17363.
def localCycle00462 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 4, .distance 0 5, .distance 1 5, .theta 1]
    constant := ![3, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .triangle 13 1, .gapLower 0 3, .gapLower 5 2, .corridorLower 1 5]

-- Original cycle de72ba5e295dcfef7c625a2d0f49c88afff7238e419c2d7a2d6325cf790b1bd2; original global index 17391.
def localCycle00463 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 5 2, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle dfa3669798550879ded2a4973c2657423bb5915fa21e4535fce3f759cd00b71f; original global index 17470.
def localCycle00464 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 6, .distance 0 5, .distance 1 5, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 11 2, .gapLower 0 4, .gapLower 5 1, .triangle 20 1, .gapLower 3 0]

-- Original cycle e094d71aa4b428e2008e43ee66854c54c7c6316fd2fab42979fb0bbd3739584b; original global index 17564.
def localCycle00465 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 0, .triangle 28 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle e1d3861a6f5a4d11b1ab925a5223d69f2f808cf7275f255d31f69ba404fa2469; original global index 17658.
def localCycle00466 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 2, .triangle 8 2, .gapLower 6 2, .triangle 23 2, .gapLower 6 0]

-- Original cycle e36f7521d9b2f9cd1cf722ab618370df53a281f91f52d0754b168257b1d32198; original global index 17787.
def localCycle00467 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 32 0, .triangle 13 0, .triangle 9 1, .gapLower 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle e4ea6eb6f92b48d3315707009cd31d15a73147b008f72259aad7830705d85720; original global index 17896.
def localCycle00468 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle e4edbc384bfe1b35d4f6eff8f53b23882a2b43196ae65794b1665678ff64b210; original global index 17897.
def localCycle00469 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, 0, -2, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 2, .gapLower 6 3, .gapLower 6 2, .triangle 13 1, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle e58133d94186ccb60f5ffea6ddb3f34c985413cfe81d8583e10207eb31a77324; original global index 17950.
def localCycle00470 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 0, .gapLower 3 0]

-- Original cycle e5f72892a1667f11ff99bd8bd67ad3538f403d039b4f56a1748b67280299aa06; original global index 17993.
def localCycle00471 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 6, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -2, -2, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.triangle 3 2, .triangle 14 2, .gapLower 6 2, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle e5fc473ef1572413f48eddee0f72e4749875f693365d1ef3f2958f14c60151b5; original global index 17996.
def localCycle00472 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 3 6, .distance 5 6, .distance 0 6, .distance 1 6, .distance 1 5, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .triangle 33 1, .gapLower 6 2, .triangle 4 1, .triangle 24 1, .gapLower 5 0]

-- Original cycle e69bc0710de5a98463e786fe1d69b376fd6564237867f0699f23fdaefa95a8b1; original global index 18035.
def localCycle00473 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 6, .distance 0 3, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .gapLower 5 3, .gapLower 0 4, .triangle 13 2, .gapLower 0 2, .gapLower 3 1, .gapLower 3 0]

-- Original cycle e6c10f23cc7ebe3de8e3cbe42c986c4d29ed30595a4588f870fa8bc092cb2298; original global index 18049.
def localCycle00474 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -2, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .gapLower 6 2, .gapLower 6 1, .triangle 23 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle e7a45e9db75cee71f81f4eb704a0aae7c2382b9388832270eeba1b9155716cb0; original global index 18117.
def localCycle00475 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 3 2, .gapLower 4 2, .gapLower 0 2]

-- Original cycle e8495013962da98ba44c21b703d711a95e7b19ec7e5d686ab600bb1a2e1dbaea; original global index 18157.
def localCycle00476 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 3 5, .distance 0 5, .distance 0 3, .distance 0 2]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.gapUpper 2 2, .gapLower 5 4, .gapLower 5 3, .gapLower 0 2, .gapLower 0 1]

-- Original cycle e84a1232b09e59efbb255cec2900b818ebb36627ac7ff68b08185097a7174e3d; original global index 18158.
def localCycle00477 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 5 6, .distance 0 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 30 0, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle e8909283bc7c983c7ccd083918fe2d1150a5c80570a7152b1804570a69377dc3; original global index 18177.
def localCycle00478 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle e909b8b0b18ae7a6ac56211ed681bf7e829daa518c029434d2673c656bbb65a9; original global index 18212.
def localCycle00479 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle e92136fcae60dade4d490859ccf5fbbac45b17206cc4aa8a613ce55b3595c6bc; original global index 18218.
def localCycle00480 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 2 6, .distance 5 6, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 30 2, .gapLower 6 3, .gapUpper 5 3]

-- Original cycle ead79f953eb9d3f8c6729a23c5f3999f41725a7fd82e32549248c207c931d1f7; original global index 18344.
def localCycle00481 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 1 5, .distance 0 1]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 5, .gapLower 5 2, .gapUpper 1 5]

-- Original cycle ebaea39b53b3f8a2861f2aa3c0ae3bb9b953f7a45b76648c7e9155fb4c4612f1; original global index 18392.
def localCycle00482 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 12 0, .triangle 13 0, .corridorLower 4 6, .thetaNext 3]

-- Original cycle ebfe4649ce6b79543576d901795a65a6cbc8ab713a7de320e0c4feaaaa262445; original global index 18420.
def localCycle00483 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle ec7e90db4487fd244fee54f55bc61f74f89c1d2e0df82dd4b6a04aa13452760b; original global index 18463.
def localCycle00484 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle ecf6ddb9936bc7d7d7078b04e87c6983a221aeb60d667fc9ea9b1a472a8c22e9; original global index 18497.
def localCycle00485 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 14 2, .gapLower 6 2, .gapUpper 5 2]

-- Original cycle ed19b058b3acbc1422fbd422999b277dec68501ddb6be169d15a7d8d9b0f60a0; original global index 18509.
def localCycle00486 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle edf721f16a35313268f9af8c295ddb13002116108abfd7832cf6e5542e931ce5; original global index 18578.
def localCycle00487 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle ee87403a7693650f9aa5119a8ceba2bd0b75905d3c7c6abc18661dfb610e8fc0; original global index 18613.
def localCycle00488 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 27 1, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle eec6400f3b5676a06ff77f1a680d8f65264845a2c5cf0502b3f346f8735efe00; original global index 18637.
def localCycle00489 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 11 2, .gapLower 0 4, .triangle 12 1, .triangle 9 1, .triangle 5 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle efa17f1a3ffbe9da04caaebc72dbbde1357ca5d76a79299960911669efd0b404; original global index 18695.
def localCycle00490 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 2, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle f10822d45f2ec9dfff533a65c98abe44d8edeab8d2ed2507a6b7a46459588990; original global index 18803.
def localCycle00491 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 6, .theta 6]
    constant := ![3, -2, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 8 2, .triangle 13 1, .triangle 23 2, .gapLower 6 0]

-- Original cycle f2250f6c7991ac0423aadce80670ff1d3ef65e63add0b47d2d32ed265f78eb89; original global index 18882.
def localCycle00492 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle f226acc00c2973711755d7f51b41d722385e85fee89d6b129d8d9f36777f0e9c; original global index 18884.
def localCycle00493 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 0, .gapLower 3 3, .triangle 11 0, .triangle 21 0, .gapLower 3 0]

-- Original cycle f22fc6ff44341188636277a8ab9a4d27d3ec48e5d76e95661098af507968f594; original global index 18888.
def localCycle00494 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 0 5, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .gapLower 5 3, .gapLower 0 4, .triangle 14 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaLower 1]

-- Original cycle f24fe2cee722f6095ebf9585a297ca5a585b92a1bdf7da66e812ef3731e7caf1; original global index 18897.
def localCycle00495 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle f2a95c89fd118af9e12db9a48ae17c1c3ccc9c73c67d06287d959251c6fd9290; original global index 18916.
def localCycle00496 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 32 0, .triangle 13 0, .triangle 6 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle f31362dd52a41a839b3dd0ffd03b7b7cda9147e36ce8501e9840a4ba7cc4f4d3; original global index 18948.
def localCycle00497 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 5 6, .distance 0 6, .distance 1 6, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .gapLower 6 2, .triangle 4 1, .triangle 21 1, .gapLower 3 0]

-- Original cycle f3abc699a30265fa8783dc12190688ccbe8d1a1519e0f390b255c3a2de02859d; original global index 19008.
def localCycle00498 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -3, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 2 2, .triangle 13 0, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle f3c6220ee036775892337abe467cd79d149724c01f62562a2d7ccb7dd0009f90; original global index 19016.
def localCycle00499 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle f3fbb6070ad0cba71cfade952d566112fc0e00717e776d556e623a8d5ffbf966; original global index 19027.
def localCycle00500 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .gapLower 4 3, .gapLower 0 3, .triangle 7 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle f5006ecaefebedd333f24fb4f79fcce9e68995aa3ea5f0aa0ce2f55046db9b5b; original global index 19103.
def localCycle00501 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 4 6, .distance 2 6, .distance 2 5]
    constant := ![2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, true] }
  origin := ![.gapUpper 5 5, .triangle 34 2, .gapLower 6 4, .triangle 30 1]

-- Original cycle f53163a619cf8b758d5e7337b0b5d0b4af38f6afa4e1d679f974455f8a4cdac1; original global index 19114.
def localCycle00502 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, -1, -3, 3, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 31 2, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle f5e6690854136b0f6896351c81cd0abaef274c6ba3891bf03f072c8530195063; original global index 19188.
def localCycle00503 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![4, 0, -1, 0, -2, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle f6be143f600dc198c1cedb182796ec692265e437c5dc492d8d12b1ea2cf2ec26; original global index 19250.
def localCycle00504 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 0 6, .distance 0 4]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 4 2, .triangle 13 2, .gapLower 0 3]

-- Original cycle f6d7e776a3837fff6ee313a7219ffc190400e21f21cc3e6aca7e216749cdc762; original global index 19253.
def localCycle00505 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 3 2, .triangle 32 1, .triangle 13 0, .gapLower 0 2]

-- Original cycle f73f833642eb85509b7d2d0166453e251963c028865659a2d1cd8058c5010fad; original global index 19286.
def localCycle00506 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 0 6, .distance 0 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 32 0, .triangle 13 2, .gapLower 0 3, .triangle 6 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle fa5cbfe9e73f5c8f2dfe85911ddf248551e2c68c0b55da7894710b86f98eeb61; original global index 19530.
def localCycle00507 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 11 2, .gapLower 6 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle fb63b8475d04fb6a442df618620294e2bbc22bfb8a431fd2280be6154ee3f409; original global index 19619.
def localCycle00508 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 2, .triangle 8 2, .gapLower 6 2, .triangle 23 1, .gapLower 6 0]

-- Original cycle fc13b622db2a22ee2e70fed3c25658f9f59d7da5db982c329224e97dcf75f440; original global index 19681.
def localCycle00509 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 9 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle fc13bfc353811fb20032440ce9ee8a3f45b2e28a193a8ecd06893890e5b300ea; original global index 19682.
def localCycle00510 : Cycle where
  length := 4
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .theta 5, .zero]
    constant := ![0, 1, -2, 0]
    coefficient := ![1, 1, -1, 0]
    strict := ![false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapUpper 5 6, .thetaLower 5]

-- Original cycle fc30e8f9a885de10fa60281ecdef744d75f8d065552bacc2829036749edf3339; original global index 19694.
def localCycle00511 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 2 2, .gapLower 5 4, .triangle 10 0, .gapLower 0 1]

-- Original cycle fd203a0a9bbbe92b6705b5192897e5d3c812a51bbd970b51855cfec68989d13f; original global index 19779.
def localCycle00512 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaLower 1]

-- Original cycle fd3c317ad74558a40a7ef8670c5ea1175142e4dc4ddd7a2b0fea5aab1238b0d6; original global index 19791.
def localCycle00513 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 4 2, .triangle 34 1, .triangle 14 0, .gapLower 0 3]

-- Original cycle fde81d4ca79a2f082cf773e38c9b2cb0c4907ac0cd71220311bd1e5836e489fe; original global index 19844.
def localCycle00514 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 0, .triangle 28 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle ff4ee4762b502204095d9890069f3e29f5779d2254e18992b5786b2ea1d92078; original global index 19960.
def localCycle00515 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 4, .distance 0 6, .distance 1 6, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .gapLower 4 3, .gapLower 0 3, .triangle 4 1, .triangle 21 1, .gapLower 3 0]

-- Original cycle ff6e03fdc9105aa89eef350eef274b706fd4622f19830a0c4e3b1adaac14906d; original global index 19971.
def localCycle00516 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 5, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 2, .triangle 14 2, .gapLower 6 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle ffdbe47c038d6ade7e749d98647159d8841f58a1d0e441327fcf657be2076df8; original global index 20015.
def localCycle00517 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 4, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![-3, 0, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true] }
  origin := ![.gapLower 0 5, .triangle 12 1, .triangle 13 0, .triangle 23 2, .gapUpper 1 5]

def library : Library := fun id => if id < 259 then (if id < 129 then (if id < 64 then (if id < 32 then (if id < 16 then (if id < 8 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none)))) else (if id < 12 then (if id < 10 then (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none)) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))) else (if id < 14 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none))))) else (if id < 24 then (if id < 20 then (if id < 18 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none))) else (if id < 22 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))) else (if id < 28 then (if id < 26 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 30 then (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)))))) else (if id < 48 then (if id < 40 then (if id < 36 then (if id < 34 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none))) else (if id < 38 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none)) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none)))) else (if id < 44 then (if id < 42 then (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none)) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none))) else (if id < 46 then (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none)) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none))))) else (if id < 56 then (if id < 52 then (if id < 50 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))) else (if id < 54 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)))) else (if id < 60 then (if id < 58 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 62 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none)) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))))))) else (if id < 96 then (if id < 80 then (if id < 72 then (if id < 68 then (if id < 66 then (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none))) else (if id < 70 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)))) else (if id < 76 then (if id < 74 then (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none))) else (if id < 78 then (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none))))) else (if id < 88 then (if id < 84 then (if id < 82 then (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none)) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none))) else (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)))) else (if id < 92 then (if id < 90 then (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none))) else (if id < 94 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)))))) else (if id < 112 then (if id < 104 then (if id < 100 then (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none))) else (if id < 102 then (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none)))) else (if id < 108 then (if id < 106 then (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none))) else (if id < 110 then (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none)) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none))))) else (if id < 120 then (if id < 116 then (if id < 114 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none))) else (if id < 118 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none)) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)))) else (if id < 124 then (if id < 122 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none))) else (if id < 126 then (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none)) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none))))))))) else (if id < 194 then (if id < 161 then (if id < 145 then (if id < 137 then (if id < 133 then (if id < 131 then (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none))) else (if id < 135 then (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)))) else (if id < 141 then (if id < 139 then (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none)) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none))) else (if id < 143 then (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none)) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none))))) else (if id < 153 then (if id < 149 then (if id < 147 then (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none)) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none))) else (if id < 151 then (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none)))) else (if id < 157 then (if id < 155 then (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none)) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none))) else (if id < 159 then (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none)) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none)))))) else (if id < 177 then (if id < 169 then (if id < 165 then (if id < 163 then (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none)) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none))) else (if id < 167 then (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none)) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none)))) else (if id < 173 then (if id < 171 then (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none)) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none))) else (if id < 175 then (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none)) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none))))) else (if id < 185 then (if id < 181 then (if id < 179 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id = 178 then some localCycle00178 else none)) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none))) else (if id < 183 then (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none)) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none)))) else (if id < 189 then (if id < 187 then (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none))) else (if id < 191 then (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none)) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id = 193 then some localCycle00193 else none)))))))) else (if id < 226 then (if id < 210 then (if id < 202 then (if id < 198 then (if id < 196 then (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none)) else (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none))) else (if id < 200 then (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none)) else (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none)))) else (if id < 206 then (if id < 204 then (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id = 203 then some localCycle00203 else none)) else (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none))) else (if id < 208 then (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none)) else (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none))))) else (if id < 218 then (if id < 214 then (if id < 212 then (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id = 211 then some localCycle00211 else none)) else (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id = 213 then some localCycle00213 else none))) else (if id < 216 then (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none)) else (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id = 217 then some localCycle00217 else none)))) else (if id < 222 then (if id < 220 then (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id = 219 then some localCycle00219 else none)) else (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id = 221 then some localCycle00221 else none))) else (if id < 224 then (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id = 223 then some localCycle00223 else none)) else (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id = 225 then some localCycle00225 else none)))))) else (if id < 242 then (if id < 234 then (if id < 230 then (if id < 228 then (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id = 227 then some localCycle00227 else none)) else (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id = 229 then some localCycle00229 else none))) else (if id < 232 then (if id < 231 then (if id = 230 then some localCycle00230 else none) else (if id = 231 then some localCycle00231 else none)) else (if id < 233 then (if id = 232 then some localCycle00232 else none) else (if id = 233 then some localCycle00233 else none)))) else (if id < 238 then (if id < 236 then (if id < 235 then (if id = 234 then some localCycle00234 else none) else (if id = 235 then some localCycle00235 else none)) else (if id < 237 then (if id = 236 then some localCycle00236 else none) else (if id = 237 then some localCycle00237 else none))) else (if id < 240 then (if id < 239 then (if id = 238 then some localCycle00238 else none) else (if id = 239 then some localCycle00239 else none)) else (if id < 241 then (if id = 240 then some localCycle00240 else none) else (if id = 241 then some localCycle00241 else none))))) else (if id < 250 then (if id < 246 then (if id < 244 then (if id < 243 then (if id = 242 then some localCycle00242 else none) else (if id = 243 then some localCycle00243 else none)) else (if id < 245 then (if id = 244 then some localCycle00244 else none) else (if id = 245 then some localCycle00245 else none))) else (if id < 248 then (if id < 247 then (if id = 246 then some localCycle00246 else none) else (if id = 247 then some localCycle00247 else none)) else (if id < 249 then (if id = 248 then some localCycle00248 else none) else (if id = 249 then some localCycle00249 else none)))) else (if id < 254 then (if id < 252 then (if id < 251 then (if id = 250 then some localCycle00250 else none) else (if id = 251 then some localCycle00251 else none)) else (if id < 253 then (if id = 252 then some localCycle00252 else none) else (if id = 253 then some localCycle00253 else none))) else (if id < 256 then (if id < 255 then (if id = 254 then some localCycle00254 else none) else (if id = 255 then some localCycle00255 else none)) else (if id < 257 then (if id = 256 then some localCycle00256 else none) else (if id < 258 then (if id = 257 then some localCycle00257 else none) else (if id = 258 then some localCycle00258 else none)))))))))) else (if id < 388 then (if id < 323 then (if id < 291 then (if id < 275 then (if id < 267 then (if id < 263 then (if id < 261 then (if id < 260 then (if id = 259 then some localCycle00259 else none) else (if id = 260 then some localCycle00260 else none)) else (if id < 262 then (if id = 261 then some localCycle00261 else none) else (if id = 262 then some localCycle00262 else none))) else (if id < 265 then (if id < 264 then (if id = 263 then some localCycle00263 else none) else (if id = 264 then some localCycle00264 else none)) else (if id < 266 then (if id = 265 then some localCycle00265 else none) else (if id = 266 then some localCycle00266 else none)))) else (if id < 271 then (if id < 269 then (if id < 268 then (if id = 267 then some localCycle00267 else none) else (if id = 268 then some localCycle00268 else none)) else (if id < 270 then (if id = 269 then some localCycle00269 else none) else (if id = 270 then some localCycle00270 else none))) else (if id < 273 then (if id < 272 then (if id = 271 then some localCycle00271 else none) else (if id = 272 then some localCycle00272 else none)) else (if id < 274 then (if id = 273 then some localCycle00273 else none) else (if id = 274 then some localCycle00274 else none))))) else (if id < 283 then (if id < 279 then (if id < 277 then (if id < 276 then (if id = 275 then some localCycle00275 else none) else (if id = 276 then some localCycle00276 else none)) else (if id < 278 then (if id = 277 then some localCycle00277 else none) else (if id = 278 then some localCycle00278 else none))) else (if id < 281 then (if id < 280 then (if id = 279 then some localCycle00279 else none) else (if id = 280 then some localCycle00280 else none)) else (if id < 282 then (if id = 281 then some localCycle00281 else none) else (if id = 282 then some localCycle00282 else none)))) else (if id < 287 then (if id < 285 then (if id < 284 then (if id = 283 then some localCycle00283 else none) else (if id = 284 then some localCycle00284 else none)) else (if id < 286 then (if id = 285 then some localCycle00285 else none) else (if id = 286 then some localCycle00286 else none))) else (if id < 289 then (if id < 288 then (if id = 287 then some localCycle00287 else none) else (if id = 288 then some localCycle00288 else none)) else (if id < 290 then (if id = 289 then some localCycle00289 else none) else (if id = 290 then some localCycle00290 else none)))))) else (if id < 307 then (if id < 299 then (if id < 295 then (if id < 293 then (if id < 292 then (if id = 291 then some localCycle00291 else none) else (if id = 292 then some localCycle00292 else none)) else (if id < 294 then (if id = 293 then some localCycle00293 else none) else (if id = 294 then some localCycle00294 else none))) else (if id < 297 then (if id < 296 then (if id = 295 then some localCycle00295 else none) else (if id = 296 then some localCycle00296 else none)) else (if id < 298 then (if id = 297 then some localCycle00297 else none) else (if id = 298 then some localCycle00298 else none)))) else (if id < 303 then (if id < 301 then (if id < 300 then (if id = 299 then some localCycle00299 else none) else (if id = 300 then some localCycle00300 else none)) else (if id < 302 then (if id = 301 then some localCycle00301 else none) else (if id = 302 then some localCycle00302 else none))) else (if id < 305 then (if id < 304 then (if id = 303 then some localCycle00303 else none) else (if id = 304 then some localCycle00304 else none)) else (if id < 306 then (if id = 305 then some localCycle00305 else none) else (if id = 306 then some localCycle00306 else none))))) else (if id < 315 then (if id < 311 then (if id < 309 then (if id < 308 then (if id = 307 then some localCycle00307 else none) else (if id = 308 then some localCycle00308 else none)) else (if id < 310 then (if id = 309 then some localCycle00309 else none) else (if id = 310 then some localCycle00310 else none))) else (if id < 313 then (if id < 312 then (if id = 311 then some localCycle00311 else none) else (if id = 312 then some localCycle00312 else none)) else (if id < 314 then (if id = 313 then some localCycle00313 else none) else (if id = 314 then some localCycle00314 else none)))) else (if id < 319 then (if id < 317 then (if id < 316 then (if id = 315 then some localCycle00315 else none) else (if id = 316 then some localCycle00316 else none)) else (if id < 318 then (if id = 317 then some localCycle00317 else none) else (if id = 318 then some localCycle00318 else none))) else (if id < 321 then (if id < 320 then (if id = 319 then some localCycle00319 else none) else (if id = 320 then some localCycle00320 else none)) else (if id < 322 then (if id = 321 then some localCycle00321 else none) else (if id = 322 then some localCycle00322 else none))))))) else (if id < 355 then (if id < 339 then (if id < 331 then (if id < 327 then (if id < 325 then (if id < 324 then (if id = 323 then some localCycle00323 else none) else (if id = 324 then some localCycle00324 else none)) else (if id < 326 then (if id = 325 then some localCycle00325 else none) else (if id = 326 then some localCycle00326 else none))) else (if id < 329 then (if id < 328 then (if id = 327 then some localCycle00327 else none) else (if id = 328 then some localCycle00328 else none)) else (if id < 330 then (if id = 329 then some localCycle00329 else none) else (if id = 330 then some localCycle00330 else none)))) else (if id < 335 then (if id < 333 then (if id < 332 then (if id = 331 then some localCycle00331 else none) else (if id = 332 then some localCycle00332 else none)) else (if id < 334 then (if id = 333 then some localCycle00333 else none) else (if id = 334 then some localCycle00334 else none))) else (if id < 337 then (if id < 336 then (if id = 335 then some localCycle00335 else none) else (if id = 336 then some localCycle00336 else none)) else (if id < 338 then (if id = 337 then some localCycle00337 else none) else (if id = 338 then some localCycle00338 else none))))) else (if id < 347 then (if id < 343 then (if id < 341 then (if id < 340 then (if id = 339 then some localCycle00339 else none) else (if id = 340 then some localCycle00340 else none)) else (if id < 342 then (if id = 341 then some localCycle00341 else none) else (if id = 342 then some localCycle00342 else none))) else (if id < 345 then (if id < 344 then (if id = 343 then some localCycle00343 else none) else (if id = 344 then some localCycle00344 else none)) else (if id < 346 then (if id = 345 then some localCycle00345 else none) else (if id = 346 then some localCycle00346 else none)))) else (if id < 351 then (if id < 349 then (if id < 348 then (if id = 347 then some localCycle00347 else none) else (if id = 348 then some localCycle00348 else none)) else (if id < 350 then (if id = 349 then some localCycle00349 else none) else (if id = 350 then some localCycle00350 else none))) else (if id < 353 then (if id < 352 then (if id = 351 then some localCycle00351 else none) else (if id = 352 then some localCycle00352 else none)) else (if id < 354 then (if id = 353 then some localCycle00353 else none) else (if id = 354 then some localCycle00354 else none)))))) else (if id < 371 then (if id < 363 then (if id < 359 then (if id < 357 then (if id < 356 then (if id = 355 then some localCycle00355 else none) else (if id = 356 then some localCycle00356 else none)) else (if id < 358 then (if id = 357 then some localCycle00357 else none) else (if id = 358 then some localCycle00358 else none))) else (if id < 361 then (if id < 360 then (if id = 359 then some localCycle00359 else none) else (if id = 360 then some localCycle00360 else none)) else (if id < 362 then (if id = 361 then some localCycle00361 else none) else (if id = 362 then some localCycle00362 else none)))) else (if id < 367 then (if id < 365 then (if id < 364 then (if id = 363 then some localCycle00363 else none) else (if id = 364 then some localCycle00364 else none)) else (if id < 366 then (if id = 365 then some localCycle00365 else none) else (if id = 366 then some localCycle00366 else none))) else (if id < 369 then (if id < 368 then (if id = 367 then some localCycle00367 else none) else (if id = 368 then some localCycle00368 else none)) else (if id < 370 then (if id = 369 then some localCycle00369 else none) else (if id = 370 then some localCycle00370 else none))))) else (if id < 379 then (if id < 375 then (if id < 373 then (if id < 372 then (if id = 371 then some localCycle00371 else none) else (if id = 372 then some localCycle00372 else none)) else (if id < 374 then (if id = 373 then some localCycle00373 else none) else (if id = 374 then some localCycle00374 else none))) else (if id < 377 then (if id < 376 then (if id = 375 then some localCycle00375 else none) else (if id = 376 then some localCycle00376 else none)) else (if id < 378 then (if id = 377 then some localCycle00377 else none) else (if id = 378 then some localCycle00378 else none)))) else (if id < 383 then (if id < 381 then (if id < 380 then (if id = 379 then some localCycle00379 else none) else (if id = 380 then some localCycle00380 else none)) else (if id < 382 then (if id = 381 then some localCycle00381 else none) else (if id = 382 then some localCycle00382 else none))) else (if id < 385 then (if id < 384 then (if id = 383 then some localCycle00383 else none) else (if id = 384 then some localCycle00384 else none)) else (if id < 386 then (if id = 385 then some localCycle00385 else none) else (if id < 387 then (if id = 386 then some localCycle00386 else none) else (if id = 387 then some localCycle00387 else none))))))))) else (if id < 453 then (if id < 420 then (if id < 404 then (if id < 396 then (if id < 392 then (if id < 390 then (if id < 389 then (if id = 388 then some localCycle00388 else none) else (if id = 389 then some localCycle00389 else none)) else (if id < 391 then (if id = 390 then some localCycle00390 else none) else (if id = 391 then some localCycle00391 else none))) else (if id < 394 then (if id < 393 then (if id = 392 then some localCycle00392 else none) else (if id = 393 then some localCycle00393 else none)) else (if id < 395 then (if id = 394 then some localCycle00394 else none) else (if id = 395 then some localCycle00395 else none)))) else (if id < 400 then (if id < 398 then (if id < 397 then (if id = 396 then some localCycle00396 else none) else (if id = 397 then some localCycle00397 else none)) else (if id < 399 then (if id = 398 then some localCycle00398 else none) else (if id = 399 then some localCycle00399 else none))) else (if id < 402 then (if id < 401 then (if id = 400 then some localCycle00400 else none) else (if id = 401 then some localCycle00401 else none)) else (if id < 403 then (if id = 402 then some localCycle00402 else none) else (if id = 403 then some localCycle00403 else none))))) else (if id < 412 then (if id < 408 then (if id < 406 then (if id < 405 then (if id = 404 then some localCycle00404 else none) else (if id = 405 then some localCycle00405 else none)) else (if id < 407 then (if id = 406 then some localCycle00406 else none) else (if id = 407 then some localCycle00407 else none))) else (if id < 410 then (if id < 409 then (if id = 408 then some localCycle00408 else none) else (if id = 409 then some localCycle00409 else none)) else (if id < 411 then (if id = 410 then some localCycle00410 else none) else (if id = 411 then some localCycle00411 else none)))) else (if id < 416 then (if id < 414 then (if id < 413 then (if id = 412 then some localCycle00412 else none) else (if id = 413 then some localCycle00413 else none)) else (if id < 415 then (if id = 414 then some localCycle00414 else none) else (if id = 415 then some localCycle00415 else none))) else (if id < 418 then (if id < 417 then (if id = 416 then some localCycle00416 else none) else (if id = 417 then some localCycle00417 else none)) else (if id < 419 then (if id = 418 then some localCycle00418 else none) else (if id = 419 then some localCycle00419 else none)))))) else (if id < 436 then (if id < 428 then (if id < 424 then (if id < 422 then (if id < 421 then (if id = 420 then some localCycle00420 else none) else (if id = 421 then some localCycle00421 else none)) else (if id < 423 then (if id = 422 then some localCycle00422 else none) else (if id = 423 then some localCycle00423 else none))) else (if id < 426 then (if id < 425 then (if id = 424 then some localCycle00424 else none) else (if id = 425 then some localCycle00425 else none)) else (if id < 427 then (if id = 426 then some localCycle00426 else none) else (if id = 427 then some localCycle00427 else none)))) else (if id < 432 then (if id < 430 then (if id < 429 then (if id = 428 then some localCycle00428 else none) else (if id = 429 then some localCycle00429 else none)) else (if id < 431 then (if id = 430 then some localCycle00430 else none) else (if id = 431 then some localCycle00431 else none))) else (if id < 434 then (if id < 433 then (if id = 432 then some localCycle00432 else none) else (if id = 433 then some localCycle00433 else none)) else (if id < 435 then (if id = 434 then some localCycle00434 else none) else (if id = 435 then some localCycle00435 else none))))) else (if id < 444 then (if id < 440 then (if id < 438 then (if id < 437 then (if id = 436 then some localCycle00436 else none) else (if id = 437 then some localCycle00437 else none)) else (if id < 439 then (if id = 438 then some localCycle00438 else none) else (if id = 439 then some localCycle00439 else none))) else (if id < 442 then (if id < 441 then (if id = 440 then some localCycle00440 else none) else (if id = 441 then some localCycle00441 else none)) else (if id < 443 then (if id = 442 then some localCycle00442 else none) else (if id = 443 then some localCycle00443 else none)))) else (if id < 448 then (if id < 446 then (if id < 445 then (if id = 444 then some localCycle00444 else none) else (if id = 445 then some localCycle00445 else none)) else (if id < 447 then (if id = 446 then some localCycle00446 else none) else (if id = 447 then some localCycle00447 else none))) else (if id < 450 then (if id < 449 then (if id = 448 then some localCycle00448 else none) else (if id = 449 then some localCycle00449 else none)) else (if id < 451 then (if id = 450 then some localCycle00450 else none) else (if id < 452 then (if id = 451 then some localCycle00451 else none) else (if id = 452 then some localCycle00452 else none)))))))) else (if id < 485 then (if id < 469 then (if id < 461 then (if id < 457 then (if id < 455 then (if id < 454 then (if id = 453 then some localCycle00453 else none) else (if id = 454 then some localCycle00454 else none)) else (if id < 456 then (if id = 455 then some localCycle00455 else none) else (if id = 456 then some localCycle00456 else none))) else (if id < 459 then (if id < 458 then (if id = 457 then some localCycle00457 else none) else (if id = 458 then some localCycle00458 else none)) else (if id < 460 then (if id = 459 then some localCycle00459 else none) else (if id = 460 then some localCycle00460 else none)))) else (if id < 465 then (if id < 463 then (if id < 462 then (if id = 461 then some localCycle00461 else none) else (if id = 462 then some localCycle00462 else none)) else (if id < 464 then (if id = 463 then some localCycle00463 else none) else (if id = 464 then some localCycle00464 else none))) else (if id < 467 then (if id < 466 then (if id = 465 then some localCycle00465 else none) else (if id = 466 then some localCycle00466 else none)) else (if id < 468 then (if id = 467 then some localCycle00467 else none) else (if id = 468 then some localCycle00468 else none))))) else (if id < 477 then (if id < 473 then (if id < 471 then (if id < 470 then (if id = 469 then some localCycle00469 else none) else (if id = 470 then some localCycle00470 else none)) else (if id < 472 then (if id = 471 then some localCycle00471 else none) else (if id = 472 then some localCycle00472 else none))) else (if id < 475 then (if id < 474 then (if id = 473 then some localCycle00473 else none) else (if id = 474 then some localCycle00474 else none)) else (if id < 476 then (if id = 475 then some localCycle00475 else none) else (if id = 476 then some localCycle00476 else none)))) else (if id < 481 then (if id < 479 then (if id < 478 then (if id = 477 then some localCycle00477 else none) else (if id = 478 then some localCycle00478 else none)) else (if id < 480 then (if id = 479 then some localCycle00479 else none) else (if id = 480 then some localCycle00480 else none))) else (if id < 483 then (if id < 482 then (if id = 481 then some localCycle00481 else none) else (if id = 482 then some localCycle00482 else none)) else (if id < 484 then (if id = 483 then some localCycle00483 else none) else (if id = 484 then some localCycle00484 else none)))))) else (if id < 501 then (if id < 493 then (if id < 489 then (if id < 487 then (if id < 486 then (if id = 485 then some localCycle00485 else none) else (if id = 486 then some localCycle00486 else none)) else (if id < 488 then (if id = 487 then some localCycle00487 else none) else (if id = 488 then some localCycle00488 else none))) else (if id < 491 then (if id < 490 then (if id = 489 then some localCycle00489 else none) else (if id = 490 then some localCycle00490 else none)) else (if id < 492 then (if id = 491 then some localCycle00491 else none) else (if id = 492 then some localCycle00492 else none)))) else (if id < 497 then (if id < 495 then (if id < 494 then (if id = 493 then some localCycle00493 else none) else (if id = 494 then some localCycle00494 else none)) else (if id < 496 then (if id = 495 then some localCycle00495 else none) else (if id = 496 then some localCycle00496 else none))) else (if id < 499 then (if id < 498 then (if id = 497 then some localCycle00497 else none) else (if id = 498 then some localCycle00498 else none)) else (if id < 500 then (if id = 499 then some localCycle00499 else none) else (if id = 500 then some localCycle00500 else none))))) else (if id < 509 then (if id < 505 then (if id < 503 then (if id < 502 then (if id = 501 then some localCycle00501 else none) else (if id = 502 then some localCycle00502 else none)) else (if id < 504 then (if id = 503 then some localCycle00503 else none) else (if id = 504 then some localCycle00504 else none))) else (if id < 507 then (if id < 506 then (if id = 505 then some localCycle00505 else none) else (if id = 506 then some localCycle00506 else none)) else (if id < 508 then (if id = 507 then some localCycle00507 else none) else (if id = 508 then some localCycle00508 else none)))) else (if id < 513 then (if id < 511 then (if id < 510 then (if id = 509 then some localCycle00509 else none) else (if id = 510 then some localCycle00510 else none)) else (if id < 512 then (if id = 511 then some localCycle00511 else none) else (if id = 512 then some localCycle00512 else none))) else (if id < 515 then (if id < 514 then (if id = 513 then some localCycle00513 else none) else (if id = 514 then some localCycle00514 else none)) else (if id < 516 then (if id = 515 then some localCycle00515 else none) else (if id < 517 then (if id = 516 then some localCycle00516 else none) else (if id = 517 then some localCycle00517 else none))))))))))

def namedLeaf000 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 5, 3, 6, 4, 0], ![1, 0, 6, 5, 3, 4], ![5, 1, 6, 0, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 1, 0, 6, 2], ![4, 1, 3, 0, 5, 2]], proof := .tail 266 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18048)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 5, 3, 6, 4, 0], ![1, 0, 6, 5, 3, 4], ![5, 1, 6, 0, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 1, 6, 0, 2], ![4, 1, 3, 5, 0, 2]], proof := .tail 159 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18049)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 5, 6, 3, 4, 0], ![1, 0, 5, 6, 3, 4], ![5, 6, 1, 0, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 1, 0, 2, 6], ![4, 3, 1, 0, 2, 5]], proof := .low6 (![133, 117, 183, 311, 298, 388, 510, 346, 418, 335, 241, 396, 396, 82, 349, 354, 368, 368, 314, 402, 53, 380, 60, 175, 364, 75, 362, 430]) }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18050)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 5, 6, 3, 4, 0], ![1, 0, 6, 5, 3, 4], ![5, 6, 1, 0, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 1, 0, 6, 2], ![4, 3, 1, 0, 5, 2]], proof := .tail 328 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18051)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 5, 6, 3, 4, 0], ![1, 0, 6, 5, 3, 4], ![5, 6, 1, 0, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 1, 6, 0, 2], ![4, 3, 1, 5, 0, 2]], proof := .tail 316 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18052)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 6, 5, 3, 4, 0], ![1, 0, 6, 5, 3, 4], ![5, 6, 1, 0, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 6, 1, 0, 2], ![4, 3, 5, 1, 0, 2]], proof := .tail 316 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18053)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 6, 5, 3, 4, 0], ![1, 0, 6, 5, 3, 4], ![6, 5, 1, 0, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 3, 1, 0, 2], ![4, 5, 3, 1, 0, 2]], proof := .tail 168 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18054)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 6, 5, 3, 4, 0], ![1, 0, 6, 5, 3, 4], ![6, 5, 1, 0, 2, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 3, 1, 0, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 385 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18055)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 3, 5, 6], ![1, 0, 4, 2, 5, 6], ![1, 0, 3, 2, 5, 6], ![1, 0, 2, 3, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 360 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18056)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 3, 5, 6], ![1, 0, 4, 2, 5, 6], ![1, 0, 3, 2, 6, 5], ![1, 0, 2, 3, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 487 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18057)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 3, 5, 6], ![1, 0, 4, 2, 6, 5], ![1, 0, 3, 2, 6, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 3, 4]], proof := .tail 383 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18058)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 3, 6, 5], ![1, 0, 4, 2, 6, 5], ![1, 0, 3, 2, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 3, 4]], proof := .low6 (![7, 259, 186, 480, 113, 401, 109, 68, 226, 389, 291, 324, 79, 403, 242, 332, 324, 79, 257, 74, 324, 79, 424, 324, 387, 23, 488, 324]) }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18059)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 3, 6, 5], ![1, 0, 4, 2, 6, 5], ![1, 0, 3, 2, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 3, 4]], proof := .low6 (![318, 69, 485, 147, 113, 401, 109, 43, 379, 10, 345, 324, 309, 471, 377, 377, 324, 377, 254, 272, 324, 91, 76, 324, 409, 23, 488, 324]) }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18060)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 4, 3, 6, 5], ![1, 0, 4, 2, 6, 5], ![1, 0, 3, 2, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low6 (![161, 413, 263, 160, 113, 401, 109, 89, 516, 45, 188, 324, 205, 212, 492, 499, 324, 394, 363, 121, 324, 79, 202, 324, 79, 23, 488, 324]) }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18061)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 6, 3, 5], ![1, 0, 4, 6, 2, 5], ![1, 0, 3, 2, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 3, 2, 4]], proof := .low6 (![444, 259, 186, 71, 240, 32, 179, 235, 90, 22, 228, 37, 408, 213, 73, 273, 56, 449, 73, 472, 66, 66, 330, 137, 137, 410, 285, 303]) }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18062)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 3, 5], ![1, 0, 4, 6, 2, 5], ![1, 0, 3, 6, 2, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 3, 4, 2]], proof := .tail 417 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18063)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![1, 0, 6, 3, 2, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 4, 3, 2]], proof := .tail 276 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18064)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 6, 3, 5], ![1, 0, 4, 6, 2, 5], ![1, 0, 3, 2, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 3, 2, 4]], proof := .low6 (![444, 69, 135, 88, 277, 32, 179, 51, 238, 334, 156, 334, 334, 471, 336, 377, 377, 377, 104, 0, 375, 320, 503, 308, 308, 24, 416, 244]) }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18065)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 3, 5], ![1, 0, 4, 6, 2, 5], ![1, 0, 3, 6, 2, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 3, 4, 2]], proof := .tail 417 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18066)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![1, 0, 6, 3, 2, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 4, 3, 2]], proof := .tail 248 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18067)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![1, 6, 0, 3, 2, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 0, 3, 2]], proof := .tail 248 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18068)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 4, 6, 3, 5], ![1, 0, 4, 6, 2, 5], ![1, 0, 3, 2, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 3, 2, 4]], proof := .low6 (![114, 65, 163, 127, 240, 32, 179, 184, 141, 16, 102, 302, 302, 366, 185, 273, 372, 81, 236, 173, 149, 371, 355, 267, 267, 410, 285, 303]) }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18069)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 3, 5], ![1, 0, 4, 6, 2, 5], ![1, 0, 3, 6, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 3, 4, 2]], proof := .tail 417 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18070)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![1, 0, 6, 3, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 4, 3, 2]], proof := .tail 98 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18071)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![1, 6, 0, 3, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 0, 3, 2]], proof := .tail 249 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18072)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![6, 1, 0, 3, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 0, 3, 2]], proof := .tail 432 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18073)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 3, 5], ![1, 6, 0, 4, 2, 5], ![1, 6, 0, 3, 2, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 3, 0, 2]], proof := .tail 157 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18074)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 3, 5], ![1, 6, 0, 4, 2, 5], ![1, 6, 0, 3, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 3, 0, 2]], proof := .tail 157 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18075)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 4, 3, 5], ![1, 6, 0, 4, 2, 5], ![6, 1, 0, 3, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 3, 0, 2]], proof := .tail 157 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18076)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 6, 3, 4, 5, 0], ![1, 0, 6, 4, 3, 5], ![6, 1, 0, 4, 2, 5], ![6, 1, 0, 3, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 288 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18077)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 5, 3, 6], ![1, 0, 4, 5, 2, 6], ![1, 0, 3, 2, 5, 6], ![1, 0, 3, 2, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .low0 (![247, 72, 475, 131, 261, 447, 96, 461, 42, 348, 425, 425, 8, 18, 461, 461, 461, 461, 271, 440, 440, 107, 61, 443, 8, 15, 8, 8]) }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18078)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 5, 3, 6], ![1, 0, 4, 5, 2, 6], ![1, 0, 3, 2, 6, 5], ![1, 0, 3, 2, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 450 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18079)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 4, 3, 6], ![1, 0, 4, 5, 2, 6], ![1, 0, 3, 5, 2, 6], ![1, 0, 3, 4, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 305 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18080)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 4, 3, 6], ![1, 0, 5, 4, 2, 6], ![1, 0, 5, 3, 2, 6], ![1, 0, 4, 3, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 97 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18081)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 4, 3, 6], ![1, 0, 5, 4, 2, 6], ![1, 5, 0, 3, 2, 6], ![1, 4, 0, 3, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 125 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18082)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 4, 3, 6], ![1, 0, 5, 4, 2, 6], ![5, 1, 0, 3, 2, 6], ![4, 1, 0, 3, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .low6 (![502, 259, 435, 191, 49, 84, 14, 120, 365, 174, 319, 392, 490, 474, 322, 319, 392, 106, 197, 319, 392, 251, 153, 215, 139, 446, 319, 392]) }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18083)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 5, 6, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 2, 5, 6], ![1, 0, 3, 2, 4, 6], ![1, 0, 3, 2, 4, 5]], proof := .low6 (![301, 259, 434, 233, 495, 110, 465, 422, 154, 209, 423, 78, 514, 29, 429, 144, 151, 514, 367, 359, 299, 514, 484, 442, 26, 166, 224, 181]) }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18084)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 5, 6, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 2, 6, 5], ![1, 0, 3, 2, 6, 4], ![1, 0, 3, 2, 5, 4]], proof := .low0 (![414, 72, 475, 313, 464, 447, 96, 461, 421, 395, 489, 353, 8, 18, 461, 461, 461, 461, 100, 440, 440, 440, 61, 443, 12, 15, 456, 8]) }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18085)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 6, 5, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 2, 6, 5], ![1, 0, 3, 6, 2, 4], ![1, 0, 3, 5, 2, 4]], proof := .low0 (![246, 72, 475, 260, 399, 447, 96, 461, 440, 453, 347, 59, 8, 18, 461, 461, 461, 461, 463, 440, 440, 440, 61, 443, 384, 15, 456, 287]) }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18086)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 6, 5, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 2, 6, 5], ![1, 0, 6, 3, 2, 4], ![1, 0, 5, 3, 2, 4]], proof := .low6 (![239, 259, 186, 70, 210, 32, 179, 477, 17, 134, 420, 37, 350, 101, 80, 378, 56, 232, 497, 170, 170, 170, 317, 200, 370, 410, 253, 303]) }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18087)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 6, 5, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 2, 6, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 0, 3, 2, 4]], proof := .low6 (![239, 69, 428, 436, 210, 32, 179, 36, 326, 439, 245, 103, 468, 471, 377, 377, 377, 377, 221, 386, 375, 252, 85, 57, 87, 24, 99, 244]) }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18088)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 4, 6, 5, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 2, 6, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 0, 3, 2, 4]], proof := .low6 (![161, 413, 369, 223, 210, 32, 179, 150, 507, 486, 192, 225, 93, 1, 483, 262, 372, 269, 227, 406, 149, 344, 284, 258, 290, 410, 253, 303]) }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18089)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 6, 2, 5], ![1, 0, 3, 6, 2, 4], ![1, 0, 3, 5, 4, 2]], proof := .tail 417 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18090)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 6, 2, 5], ![1, 0, 6, 3, 2, 4], ![1, 0, 5, 3, 4, 2]], proof := .tail 417 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18091)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 6, 2, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 0, 3, 4, 2]], proof := .tail 417 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18092)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 5, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 6, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 0, 3, 4, 2]], proof := .tail 417 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18093)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 2], ![1, 0, 6, 3, 2, 5], ![1, 0, 6, 3, 2, 4], ![1, 0, 5, 4, 3, 2]], proof := .low0 (![105, 2, 111, 255, 92, 447, 96, 13, 339, 513, 433, 130, 8, 505, 108, 196, 208, 208, 513, 211, 505, 505, 280, 513, 513, 15, 6, 287]) }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18094)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 2], ![1, 0, 6, 3, 2, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 0, 4, 3, 2]], proof := .low0 (![496, 2, 111, 504, 455, 282, 96, 467, 339, 506, 325, 327, 338, 505, 292, 208, 327, 208, 115, 505, 327, 505, 132, 327, 426, 327, 494, 333]) }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18095)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 2], ![1, 0, 6, 3, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 0, 4, 3, 2]], proof := .low0 (![496, 2, 111, 504, 38, 481, 96, 467, 339, 506, 130, 358, 55, 505, 292, 208, 208, 208, 115, 505, 505, 505, 132, 256, 189, 381, 152, 390]) }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18096)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 2], ![1, 6, 0, 3, 2, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 4, 0, 3, 2]], proof := .low0 (![46, 2, 28, 304, 95, 517, 96, 208, 216, 374, 158, 62, 458, 445, 208, 158, 62, 208, 323, 158, 62, 8, 315, 62, 407, 3, 158, 343]) }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18097)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 2], ![1, 6, 0, 3, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 4, 0, 3, 2]], proof := .low0 (![46, 2, 28, 143, 67, 30, 96, 208, 216, 374, 33, 358, 180, 445, 208, 33, 77, 208, 323, 473, 293, 8, 136, 312, 407, 193, 33, 343]) }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18098)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 2], ![6, 1, 0, 3, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 4, 1, 0, 3, 2]], proof := .low0 (![46, 2, 28, 515, 195, 481, 96, 208, 216, 374, 268, 199, 8, 445, 208, 208, 124, 208, 341, 473, 293, 8, 220, 204, 8, 25, 268, 415]) }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18099)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 4, 6, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 5, 2, 6], ![1, 0, 3, 4, 2, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 305 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18100)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 5, 6, 2], ![1, 0, 3, 4, 2, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 203 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18101)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 5, 6, 2], ![1, 0, 3, 4, 6, 2], ![1, 0, 3, 4, 5, 2]], proof := .tail 274 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18102)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 6, 5, 2], ![1, 0, 3, 6, 4, 2], ![1, 0, 3, 5, 4, 2]], proof := .tail 167 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18103)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 6, 5, 2], ![1, 0, 6, 3, 4, 2], ![1, 0, 5, 3, 4, 2]], proof := .tail 34 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18104)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 6, 5, 2], ![1, 6, 0, 3, 4, 2], ![1, 5, 0, 3, 4, 2]], proof := .tail 34 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18105)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 6, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 1, 0, 3, 4, 2]], proof := .tail 34 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18106)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 4, 5, 2], ![1, 0, 6, 3, 5, 2], ![1, 0, 6, 3, 4, 2], ![1, 0, 5, 4, 3, 2]], proof := .tail 63 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18107)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 4, 5, 2], ![1, 0, 6, 3, 5, 2], ![1, 6, 0, 3, 4, 2], ![1, 5, 0, 4, 3, 2]], proof := .tail 63 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18108)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 4, 5, 2], ![1, 0, 6, 3, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 1, 0, 4, 3, 2]], proof := .tail 20 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18109)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 4, 5, 2], ![1, 6, 0, 3, 5, 2], ![1, 6, 0, 3, 4, 2], ![1, 5, 4, 0, 3, 2]], proof := .tail 265 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18110)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 4, 5, 2], ![1, 6, 0, 3, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 1, 4, 0, 3, 2]], proof := .tail 265 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18111)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 4, 5, 2], ![6, 1, 0, 3, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 4, 1, 0, 3, 2]], proof := .tail 118 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18112)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 4, 6, 3], ![1, 0, 5, 4, 6, 2], ![1, 0, 5, 3, 2, 6], ![1, 0, 4, 3, 2, 6], ![1, 0, 3, 2, 4, 5]], proof := .low6 (![162, 259, 434, 233, 321, 84, 155, 422, 154, 209, 190, 392, 123, 29, 429, 501, 392, 146, 367, 501, 392, 123, 484, 392, 454, 119, 140, 392]) }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18113)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 0, 5, 4, 6, 2], ![1, 0, 5, 3, 6, 2], ![1, 0, 4, 3, 2, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 295 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18114)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 5, 4, 6, 2], ![1, 0, 5, 3, 6, 2], ![1, 0, 4, 3, 6, 2], ![1, 0, 3, 4, 5, 2]], proof := .tail 331 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18115)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 2], ![1, 0, 5, 6, 3, 2], ![1, 0, 4, 3, 2, 6], ![1, 0, 4, 3, 2, 5]], proof := .low6 (![419, 259, 427, 50, 126, 388, 510, 54, 243, 4, 361, 275, 201, 169, 83, 405, 281, 283, 9, 376, 376, 376, 404, 40, 41, 31, 5, 430]) }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18116)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 5, 6, 4, 2], ![1, 0, 5, 6, 3, 2], ![1, 0, 4, 3, 6, 2], ![1, 0, 4, 3, 5, 2]], proof := .tail 39 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18117)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 0, 5, 6, 3, 2], ![1, 0, 4, 6, 3, 2], ![1, 0, 4, 5, 3, 2]], proof := .tail 479 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18118)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 0, 6, 5, 3, 2], ![1, 0, 6, 4, 3, 2], ![1, 0, 5, 4, 3, 2]], proof := .tail 19 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18119)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 0, 6, 5, 3, 2], ![1, 6, 0, 4, 3, 2], ![1, 5, 0, 4, 3, 2]], proof := .tail 512 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18120)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 0, 6, 5, 3, 2], ![6, 1, 0, 4, 3, 2], ![5, 1, 0, 4, 3, 2]], proof := .tail 356 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18121)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 6, 0, 5, 3, 2], ![1, 6, 0, 4, 3, 2], ![1, 5, 4, 0, 3, 2]], proof := .tail 21 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18122)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 6, 0, 5, 3, 2], ![6, 1, 0, 4, 3, 2], ![5, 1, 4, 0, 3, 2]], proof := .tail 21 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18123)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![6, 1, 0, 5, 3, 2], ![6, 1, 0, 4, 3, 2], ![5, 4, 1, 0, 3, 2]], proof := .tail 482 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18124)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 4, 6, 3], ![1, 0, 5, 4, 6, 2], ![1, 5, 0, 3, 2, 6], ![1, 4, 0, 3, 2, 6], ![1, 0, 3, 2, 4, 5]], proof := .low6 (![222, 259, 441, 233, 321, 84, 47, 422, 48, 391, 190, 392, 187, 382, 429, 501, 392, 337, 469, 48, 392, 48, 351, 392, 218, 119, 94, 392]) }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18125)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 0, 5, 4, 6, 2], ![1, 5, 0, 3, 6, 2], ![1, 4, 0, 3, 2, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 122 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18126)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 2], ![1, 5, 0, 6, 3, 2], ![1, 4, 0, 3, 2, 6], ![1, 0, 4, 3, 2, 5]], proof := .tail 145 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18127)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 5, 4, 6, 2], ![1, 5, 0, 3, 6, 2], ![1, 4, 0, 3, 6, 2], ![1, 0, 3, 4, 5, 2]], proof := .tail 264 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18128)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 5, 6, 4, 2], ![1, 5, 0, 6, 3, 2], ![1, 4, 0, 3, 6, 2], ![1, 0, 4, 3, 5, 2]], proof := .tail 145 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18129)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 5, 0, 6, 3, 2], ![1, 4, 0, 6, 3, 2], ![1, 0, 4, 5, 3, 2]], proof := .tail 479 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18130)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 2], ![1, 5, 6, 0, 3, 2], ![1, 4, 0, 3, 2, 6], ![1, 4, 0, 3, 2, 5]], proof := .low6 (![419, 498, 234, 411, 171, 388, 297, 478, 466, 229, 165, 491, 230, 27, 307, 307, 307, 307, 164, 176, 182, 138, 194, 296, 86, 44, 300, 373]) }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18131)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 5, 6, 4, 2], ![1, 5, 6, 0, 3, 2], ![1, 4, 0, 3, 6, 2], ![1, 4, 0, 3, 5, 2]], proof := .tail 129 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18132)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 5, 6, 0, 3, 2], ![1, 4, 0, 6, 3, 2], ![1, 4, 0, 5, 3, 2]], proof := .tail 479 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18133)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 5, 6, 0, 3, 2], ![1, 4, 6, 0, 3, 2], ![1, 4, 5, 0, 3, 2]], proof := .tail 479 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18134)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 6, 5, 0, 3, 2], ![1, 6, 4, 0, 3, 2], ![1, 5, 4, 0, 3, 2]], proof := .tail 512 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18135)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 6, 5, 0, 3, 2], ![6, 1, 4, 0, 3, 2], ![5, 1, 4, 0, 3, 2]], proof := .tail 398 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18136)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![6, 1, 5, 0, 3, 2], ![6, 1, 4, 0, 3, 2], ![5, 4, 1, 0, 3, 2]], proof := .tail 177 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18137)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 4, 6, 3], ![1, 0, 5, 4, 6, 2], ![5, 1, 0, 3, 2, 6], ![4, 1, 0, 3, 2, 6], ![1, 0, 3, 2, 4, 5]], proof := .low0 (![431, 400, 437, 357, 142, 447, 96, 511, 178, 500, 289, 59, 8, 476, 511, 511, 511, 511, 279, 460, 460, 460, 207, 462, 8, 310, 329, 206]) }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18138)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 0, 5, 4, 6, 2], ![5, 1, 0, 3, 6, 2], ![4, 1, 0, 3, 2, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 509 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18139)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 2], ![5, 1, 0, 6, 3, 2], ![4, 1, 0, 3, 2, 6], ![1, 0, 4, 3, 2, 5]], proof := .tail 340 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18140)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 5, 4, 6, 2], ![5, 1, 0, 3, 6, 2], ![4, 1, 0, 3, 6, 2], ![1, 0, 3, 4, 5, 2]], proof := .tail 342 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18141)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 5, 6, 4, 2], ![5, 1, 0, 6, 3, 2], ![4, 1, 0, 3, 6, 2], ![1, 0, 4, 3, 5, 2]], proof := .tail 340 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18142)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![5, 1, 0, 6, 3, 2], ![4, 1, 0, 6, 3, 2], ![1, 0, 4, 5, 3, 2]], proof := .tail 112 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18143)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 1, 0, 3, 2, 6], ![1, 4, 0, 3, 2, 5]], proof := .tail 340 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18144)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 5, 6, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 1, 0, 3, 6, 2], ![1, 4, 0, 3, 5, 2]], proof := .tail 340 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18145)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 1, 0, 6, 3, 2], ![1, 4, 0, 5, 3, 2]], proof := .tail 112 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18146)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 1, 6, 0, 3, 2], ![1, 4, 5, 0, 3, 2]], proof := .tail 112 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18147)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 1, 0, 3, 2, 6], ![4, 1, 0, 3, 2, 5]], proof := .low6 (![52, 217, 352, 452, 126, 388, 510, 219, 508, 214, 231, 457, 116, 286, 393, 198, 448, 64, 451, 148, 58, 278, 306, 412, 397, 31, 5, 430]) }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18148)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 5, 6, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 1, 0, 3, 6, 2], ![4, 1, 0, 3, 5, 2]], proof := .tail 129 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18149)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 1, 0, 6, 3, 2], ![4, 1, 0, 5, 3, 2]], proof := .tail 35 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18150)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 1, 6, 0, 3, 2], ![4, 1, 5, 0, 3, 2]], proof := .tail 35 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18151)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 6, 1, 0, 3, 2], ![4, 5, 1, 0, 3, 2]], proof := .tail 35 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18152)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![6, 5, 1, 0, 3, 2], ![6, 4, 1, 0, 3, 2], ![5, 4, 1, 0, 3, 2]], proof := .tail 438 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18153)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 6, 0, 4, 5, 2], ![1, 6, 0, 3, 2, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 4, 3, 0, 2]], proof := .tail 294 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18154)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 4, 5, 2], ![1, 6, 0, 3, 5, 2], ![1, 6, 0, 3, 4, 2], ![1, 5, 4, 3, 0, 2]], proof := .tail 493 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18155)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 5, 4, 2], ![1, 6, 0, 5, 3, 2], ![1, 6, 0, 4, 3, 2], ![1, 5, 4, 3, 0, 2]], proof := .tail 21 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18156)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 5, 4, 2], ![1, 5, 6, 0, 3, 2], ![1, 4, 6, 0, 3, 2], ![1, 4, 5, 3, 0, 2]], proof := .tail 11 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18157)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 5, 4, 2], ![1, 6, 5, 0, 3, 2], ![1, 6, 4, 0, 3, 2], ![1, 5, 4, 3, 0, 2]], proof := .tail 470 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18158)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 5, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 1, 6, 0, 3, 2], ![1, 4, 5, 3, 0, 2]], proof := .tail 172 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18159)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 5, 3], ![1, 6, 0, 4, 5, 2], ![1, 6, 0, 3, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 4, 3, 0, 2]], proof := .tail 294 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18160)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 4, 5, 2], ![1, 6, 0, 3, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 1, 4, 3, 0, 2]], proof := .tail 493 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18161)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 5, 4, 2], ![1, 6, 0, 5, 3, 2], ![6, 1, 0, 4, 3, 2], ![5, 1, 4, 3, 0, 2]], proof := .tail 21 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18162)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 5, 4, 2], ![1, 6, 5, 0, 3, 2], ![6, 1, 4, 0, 3, 2], ![5, 1, 4, 3, 0, 2]], proof := .tail 470 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18163)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 5, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 1, 6, 0, 3, 2], ![4, 1, 5, 3, 0, 2]], proof := .tail 470 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18164)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 4, 5, 3], ![1, 6, 0, 4, 5, 2], ![6, 1, 0, 3, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 4, 1, 3, 0, 2]], proof := .tail 294 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18165)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 4, 5, 2], ![6, 1, 0, 3, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 4, 1, 3, 0, 2]], proof := .tail 493 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18166)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 5, 4, 2], ![6, 1, 0, 5, 3, 2], ![6, 1, 0, 4, 3, 2], ![5, 4, 1, 3, 0, 2]], proof := .tail 250 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18167)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 5, 4, 2], ![6, 1, 5, 0, 3, 2], ![6, 1, 4, 0, 3, 2], ![5, 4, 1, 3, 0, 2]], proof := .tail 470 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18168)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 5, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 6, 1, 0, 3, 2], ![4, 5, 1, 3, 0, 2]], proof := .tail 470 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18169)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 5, 4, 2], ![6, 5, 1, 0, 3, 2], ![6, 4, 1, 0, 3, 2], ![5, 4, 1, 3, 0, 2]], proof := .tail 470 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18170)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 6, 3, 4, 5, 0], ![1, 0, 6, 4, 5, 3], ![6, 1, 0, 4, 5, 2], ![6, 1, 0, 3, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 237 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18171)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 6, 3, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![6, 1, 0, 4, 5, 2], ![6, 1, 0, 3, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 128 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18172)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 6, 3, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![6, 1, 0, 5, 4, 2], ![6, 1, 0, 5, 3, 2], ![6, 1, 0, 4, 3, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 270 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18173)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 6, 3, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![6, 1, 0, 5, 4, 2], ![6, 1, 5, 0, 3, 2], ![6, 1, 4, 0, 3, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 177 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18174)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 6, 3, 5, 4, 0], ![1, 0, 6, 5, 4, 3], ![6, 1, 0, 5, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 6, 1, 0, 3, 2], ![4, 5, 3, 1, 0, 2]], proof := .tail 459 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18175)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (18048 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 18048 ≤ id.val) (hhigh : id.val < 18176) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 18048)) = true := by
  let j : Fin 128 := ⟨id.val - 18048, by omega⟩
  have hsum : 18048 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (18048 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard141
