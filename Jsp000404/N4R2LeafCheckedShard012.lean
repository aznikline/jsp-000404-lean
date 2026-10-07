import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard012
open N4R2RowDataReplay

-- Original cycle 007e68be7cd0d8d991873d795217cc2f1ca5850bd3155f7b1a835980fdfed811; original global index 45.
def localCycle00000 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, -2, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 4, .triangle 21 1, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 0093b840213dcc303e0302caf2a98fcd51973a5c210bf29422cba2556f5f4b22; original global index 50.
def localCycle00001 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 00d3860ce3596994dc0e291c08fa3ca8e6dd3432ba8b6c7503f22c2cf4a2f470; original global index 74.
def localCycle00002 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .gapLower 4 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 00e321f98e521cdf47467d7dd608d430c948d48e51d5ab75bf08154f6f9fc88e; original global index 76.
def localCycle00003 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 0 3, .theta 3]
    constant := ![3, 0, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 2, .gapLower 6 2, .triangle 11 1, .gapLower 3 0]

-- Original cycle 020d4988fe3d91019a5a0b692d3b67d12a267170f3be7aaf671125c3a0247eb1; original global index 167.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 3 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 18 2, .triangle 21 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

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

-- Original cycle 0392e1e4bca978ce5f53586037e6fc5fe7f4a030b2dfa004011085a6cfdf3ea7; original global index 287.
def localCycle00007 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 20 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 03a136791c0310615e05d7fc1a1831bb9be237eb3665891bc0ba5b45e53de56c; original global index 295.
def localCycle00008 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 03d1838b989d4a3140bd440d0f11abd4117db450ee54491bd9b5498a0647d65f; original global index 308.
def localCycle00009 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 0, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 053374a2e5bd13733c1d146a2596fad19ec8239b2422eb478d9112209752f7fc; original global index 421.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 0590f6e61aeed64c8ec20a57b77ad10b7a4f0ef43c4f96ed7342253efac87e80; original global index 460.
def localCycle00011 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 4, .distance 4 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 2, .triangle 13 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 065258cd52c3d2327db673ce4acb7584a411a9474b042929eb1aadc0fe21672d; original global index 520.
def localCycle00012 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 27 1, .triangle 26 0, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 0664c3211efc915e01abe61b64550af2b525736f07b485fd346cd42bb6720614; original global index 526.
def localCycle00013 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 18 2, .gapLower 6 3, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 078f5d91495c3227998baa88d47de9bd777f9e3642a0c945d23211436fc64943; original global index 619.
def localCycle00014 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 8 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 07fa26d683045916cf82496c6a91e11e7309de9a4818d9c9032e009dcb2f3d79; original global index 644.
def localCycle00015 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 0, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 0834bcb07ae67b42fc6fdd38b5e89fafa12f52033c2a72b2439bbcfb537b81ec; original global index 656.
def localCycle00016 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 2 6, .distance 2 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 27 1]

-- Original cycle 09cc969a8a278c6029ec2e54a82ad55b8d64b3b590d4cff78121cafe9c6722fa; original global index 786.
def localCycle00017 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 1, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 0a5786efd40b46064c3fab02b857cfda851ce87c0aee37afd52d99faed0b6980; original global index 825.
def localCycle00018 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 2 6, .distance 5 6, .distance 2 5]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 30 2, .gapLower 6 4, .gapUpper 5 4]

-- Original cycle 0affd810a23d5e40097397e8cf97088afde47cf0fe31bfd0339a05fa43da95c8; original global index 879.
def localCycle00019 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 1 6, .distance 1 5]
    constant := ![2, -2, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 24 1]

-- Original cycle 0c1734debb80a14fc5dcda480381170092b50bd359fbc9a9b19584517429fbee; original global index 954.
def localCycle00020 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 20 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 0c2b21414ada677d803973acfde5a135204e93bf1245fd86e67ad0a46ea15522; original global index 962.
def localCycle00021 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 4, .triangle 33 1, .triangle 20 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 0caf423a7e8db9b4b42fea4684d9f2dbfe51a27449dfa04b08196aed91b14ef1; original global index 1003.
def localCycle00022 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 0e0dcf95a94e86b464f51fadd03fb3b76364e7e9c5a5eba6a1f40b2969a49660; original global index 1104.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Original cycle 0e16c58f7d0d0e83eab01a2b4261867469baea7e81314f5e440a06965b83c0ce; original global index 1110.
def localCycle00024 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 18 2, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 0e9f92289fd6a6a63a3f99b0db277813d70b5b22def433110f28ce9d04647de7; original global index 1154.
def localCycle00025 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 5, .triangle 24 1, .triangle 33 2, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 0f5f8b157c04abfa4714b927429ea9dd6234e98bf7a251851f5b823cd3a2ea0d; original global index 1221.
def localCycle00026 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 0fb80b495db89a61153ca2f4d2a33aa046e873e83a94b94db79b72028cc9fbd8; original global index 1254.
def localCycle00027 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 2, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 10d2b9a510d02ddc2b1f07ab0e1ebad62d4aa5e85c5e496beacbebfb69c20495; original global index 1348.
def localCycle00028 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .gapLower 6 4, .triangle 4 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 111a2c01b9baeaa9cf7436c5e3934a4ca297bd3aabfa0ae56a7f5f86f47162db; original global index 1365.
def localCycle00029 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 113e6edf5185083f5ea3caf88b0884598f8fdd89b5dfa32d114f967659f5031a; original global index 1369.
def localCycle00030 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 1177dee04463558eb77ec4a6e148a5699b35d88995f8dcee195188e8755f2dba; original global index 1395.
def localCycle00031 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 3, .triangle 18 1, .triangle 17 0, .triangle 26 1, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 11c5a69b52c7afc4117696324b2a51d368c40ef01b3dfb6417072c5f23d932ad; original global index 1413.
def localCycle00032 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 2 6, .distance 5 6, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 30 2, .gapLower 6 4, .gapUpper 5 4]

-- Original cycle 12f252847fdbcde56d3953677430447c5724755577df24e38483d0a5c35a5c13; original global index 1492.
def localCycle00033 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 13526301b7cbc4a91e17d8e123fd9c341913e00441ea5ccb713479c0dc75a687; original global index 1522.
def localCycle00034 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .gapLower 6 3, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 13a00d6812dbb6fb1fe1dc1fa97caae71969b1eeab626802fbb9309cee1e46d2; original global index 1549.
def localCycle00035 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 1421047912c965276fe37983ce4db0c62f9d2ee8dbd7f906c3090ea53640bf75; original global index 1591.
def localCycle00036 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 2 6, .distance 1 2]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 18 2, .gapLower 6 3, .gapUpper 2 4]

-- Original cycle 14a2cae59c8e72611dfec7693acf3c42df5d55965cfc68a4159ec6388c773599; original global index 1637.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 11 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 162ec75e1796107d4de7a2e8390eabc79e48951ca234ea169ecb97326e27110d; original global index 1751.
def localCycle00038 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 2, .triangle 21 0, .triangle 33 1, .triangle 26 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 17608ad23ca18bcc1032adc4ea1f6e29d524f23ae87d5d37189cb997e9205efd; original global index 1834.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![2, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false, true] }
  origin := ![.gapUpper 1 1, .triangle 24 1, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 26 0, .triangle 10 0, .triangle 1 1]

-- Original cycle 17a0e0ad45fa34a6a54dcbb4c6495220a4c54e23a55adcfc6c7f984df2cb43bd; original global index 1847.
def localCycle00040 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 18 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 199e1c3a27fd84e08566b77f8d45c3dad46f10edc13fa15502f99ded69586290; original global index 2001.
def localCycle00041 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 1b28dff94edba3354fd308506f9f0d275cf882869fb3214b2db16173148e02e4; original global index 2103.
def localCycle00042 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 0, .triangle 17 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 1bd6a453ca17976b8d0e5f7e3fa8f89b5a143f051aa6af1415a8e65cc52cce1b; original global index 2153.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 6, .distance 0 3, .theta 3]
    constant := ![3, 0, 0, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .gapLower 6 2, .triangle 11 1, .gapLower 3 0]

-- Original cycle 1c550dd6bcef85a1504efad0aa6474e2b1c13af64231757cadea2170cee28e41; original global index 2177.
def localCycle00044 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 1ce58b3d8a89a61adf0191db6c78a4a90800bb1e30fbdd819edab05791291ed4; original global index 2228.
def localCycle00045 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 1e79376708361998951de32f422352a4ad29eb17fab8e114ba35b92b16592ab9; original global index 2340.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .gapLower 6 4, .triangle 24 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 1e986e59de2eee6d7d4f91dc97054d4fc69200b3149733e3f62d1231c9a9ac12; original global index 2348.
def localCycle00047 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 1edc935bb19e520cb0298db42a92cec136474b19dcba336cb3ceee2ab7f1df86; original global index 2371.
def localCycle00048 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 18 2, .triangle 24 1, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 1f8ec2bcf176ec2fb2e3f0f0b16a2bacc7061f9e3481edf69c105eae42a77ca7; original global index 2427.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 3, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 2, .triangle 21 0, .triangle 11 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 21cb4fedccac8233da105e5be3ae96865783fc114479c0c29e083b528153d5ef; original global index 2591.
def localCycle00050 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 227f6a493c616b231f78ecc2b6fac89880ba8c4142ef628dace8663a3a4715c1; original global index 2640.
def localCycle00051 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 22d67ee44a7705e5224bb51e42c68e85211a97606827e8b5368dadeec08266d4; original global index 2665.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .triangle 34 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 23a889582aa133e5427c577004c28844293bd1f1c862608dfb1e5eaf626276b5; original global index 2735.
def localCycle00053 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 24fb88f40b2dbb7ac0f8a825286561646811167114fb45c29acb39185daf1f6f; original global index 2836.
def localCycle00054 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 0, .gapLower 6 3, .triangle 4 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 25061b1f257d3f4cc8e9b929e334f8fb0f09ac363316c8522a67cb0f4077a806; original global index 2842.
def localCycle00055 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 25671f91f6e70f85da07223085d49baf010cfa71886305f866e8b1b2cb802cbd; original global index 2877.
def localCycle00056 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 25b53f8a81ffa76b94c95c6969290e82975fd5e482b9863341fc891d96b7690b; original global index 2894.
def localCycle00057 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .theta 6, .distance 5 6, .distance 2 5, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, 2, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .gapLower 6 0, .gapLower 6 6, .triangle 30 0, .triangle 26 1, .triangle 20 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 26200180412aebf5a962e308fe013e1243589288f46f4ec5c7d3d2675673239e; original global index 2920.
def localCycle00058 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .gapLower 6 4, .triangle 18 1, .triangle 15 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 27c497859e27e7c6e286c11c6e6a6a56280054e21d89d59eb630e39e19fd4fa7; original global index 3040.
def localCycle00059 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 2857ed113892a1c0aacd9d240192cc1f74d21b5f36f17e735d34e62462e1a26c; original global index 3095.
def localCycle00060 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 6 3, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 29b419966c09a13c5a7043e7cdd5589ca3fcfa7bb4a946d309c77829fbd53ae4; original global index 3182.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 29e74b5373547d17127fc1b491b3ffd475c9f1bb18327f5f1c82b2e8323a1e93; original global index 3197.
def localCycle00062 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 5 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 30 1, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 2a0418d88f1ecd015670210a7b98326a08f73f22d5425f68ca2ba726ec243c68; original global index 3204.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 18 2, .gapLower 6 3, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 2a5e02c26e3e4bb66b97efd944f6c7cec38383ba6953d3ba462e2af7a0f9e841; original global index 3230.
def localCycle00064 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 13 2, .gapLower 6 1, .gapUpper 4 2]

-- Original cycle 2aa59bd67a9016760d57f06eacf5dfd7975f0103bc0d94926a02e8c71d9629c5; original global index 3244.
def localCycle00065 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 2bc87d47a2697ca4d6b7488e290b5dcd1141afc8be4064540e4e74dee47b87d6; original global index 3347.
def localCycle00066 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 4, .distance 4 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 2, .triangle 13 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 2c8812b28e88198787c9f00bbe232e3db3a19f6a1e2d8d746afee60b7ebf37c3; original global index 3402.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .triangle 18 2, .gapLower 6 3, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 2ca06c2a328f51e0c2501db37246bc334faa8f42c14b3e9703636934f8db3006; original global index 3410.
def localCycle00068 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 2ca1f6241522b08a6a8f1c74fb907c3d83ce675cb15788cf11c228ac1c747c97; original global index 3412.
def localCycle00069 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .gapLower 6 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 2eac81d84fd46b27f68e3be5051602e0f54ad466c77735d03c68dd00ec965b4a; original global index 3570.
def localCycle00070 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 2f95a6fcea7b5bddb2e2966734c71d2eb95c76f5a1924dc847718a86367ebe30; original global index 3636.
def localCycle00071 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 20 1, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 30c74e5bd7c02d8fe3f832692c5997689fcdebbc515b535d6a401260d1e9fe20; original global index 3721.
def localCycle00072 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle 30e6ce3a7a0bad9350fc1fd4f0ed82642044bdc0d0d27d84955bb60bc269c0b7; original global index 3729.
def localCycle00073 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .triangle 21 1]

-- Original cycle 315e923d50c0a9edd49cc1b8fa101420106a5d0f1681631868401e248589ba83; original global index 3763.
def localCycle00074 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 6, .theta 6, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -2, 2, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 0, .gapLower 6 0, .gapLower 6 6, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Original cycle 32503f1a94d936560b03478d9afae744a387939488786b6c7f919b51539a6c1e; original global index 3843.
def localCycle00075 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle 3254554d272fd06fe60e64f6556dec590829a3e0c6ee37df27a8ec1ad163c911; original global index 3847.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 2 3, .distance 3 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 27 1, .triangle 25 0, .triangle 9 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 32586129e4706857a632092772467ea9318dd12019756c815f96e5634c4c6336; original global index 3849.
def localCycle00077 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 18 0, .gapLower 1 3, .triangle 20 0, .triangle 26 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 32ce5f7a9e7268c6af2f3ed90b15354fee861401e4457f0ec588f4185a10b4b6; original global index 3891.
def localCycle00078 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 335b4fec4717c48a13f406f64b88f3e11058dc38fa7dc1cc192c8b237160ab47; original global index 3931.
def localCycle00079 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 34362967c3a28383fa6a6ff76ead39386835e57175c1136fe71a6058b0ce1ef7; original global index 4001.
def localCycle00080 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 344868f0846cf0debb72e25aefeb75d0e27d8453ff1c5c366c164d2952d7dbb3; original global index 4005.
def localCycle00081 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 34eb9a5b4b67e3f14ca12a85f31176ee4311843abbbfaa330b606505d6423464; original global index 4049.
def localCycle00082 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 18 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 3502f635256d23fdf1ec38c895de2937efbbbc5d3732726b271c4aeed1758bfc; original global index 4057.
def localCycle00083 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 2, .gapLower 6 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 360a0af0f9d96c0f40de7761311eca9094c8771f545c015123fcaecd3e15e0f6; original global index 4149.
def localCycle00084 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .theta 6, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -2, 3, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 32 1, .gapLower 6 0, .corridorUpper 5 6, .gapLower 6 5, .triangle 18 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 368df2626ca45afa1a79b8eae932b2ba95e23423dce56dea6e2b868298b9f46d; original global index 4190.
def localCycle00085 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 21 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 37285485124530ccc70ec42f4d682cf2f23682fc73015d2b9b763218714aa475; original global index 4233.
def localCycle00086 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 3814ee5c581c8e5c846d612606b2a85a1e271f8d42170ffd943f9265a47d1e09; original global index 4304.
def localCycle00087 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 5, .triangle 30 0, .triangle 33 2, .gapLower 6 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 38d721e11610d21748237ab1d45dcde7e97bb450c9ba2068a65afc65fc6e571b; original global index 4376.
def localCycle00088 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 6, .distance 0 3, .theta 3]
    constant := ![3, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .gapLower 6 2, .triangle 11 1, .gapLower 3 0]

-- Original cycle 3966ea276db23fb0e1c65ab9e7efe21fa833bb09b13c4571d0633ca73d6c6e8a; original global index 4422.
def localCycle00089 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 3 6, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -2, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 18 2, .gapLower 6 3, .triangle 11 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 399183be39d113a17b3a05eab3a841a17c5bc4cdda4ed3b2cce0d9718629ce99; original global index 4436.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -1, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 13 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 3a505608d7644894c59ee29a5cf262b026f2745f29ee3a83d583a5dbae9393c8; original global index 4503.
def localCycle00091 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .triangle 33 2, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 3b06ad2d86b9d10a5cf79e675dc3fc0a863f3a47067e510c14dd03cece0760c8; original global index 4559.
def localCycle00092 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 2 6, .distance 2 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .triangle 27 1]

-- Original cycle 3d3c71d4bc119d34e915c3bfea2ecaa388709dd659f8504f12f71202ac9d15aa; original global index 4742.
def localCycle00093 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .gapLower 6 3, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 3d4b1120274a2630565f6b9e7861c2333a5d8be69400e96b476f947924925b67; original global index 4748.
def localCycle00094 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 6 1, .gapLower 6 0]

-- Original cycle 3e0da6107b96c236d21afe372228e0025aa1784860324afdb48867d82d559778; original global index 4798.
def localCycle00095 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .gapLower 6 4, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 3e2ddbbecf9d45ec2e0f0fa268a2e529efb1a08b05c1b3e7d99fa24f5a8e20bb; original global index 4811.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 4078235692219907c046ce7627a23c815904bda7cdae0181707e02674c6feed1; original global index 4982.
def localCycle00097 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 40ac7453c8a465d646d441af02b925c6e570d4e91e0d5a8e77fcdc4d09083fe8; original global index 4997.
def localCycle00098 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 6 5, .triangle 18 0]

-- Original cycle 414fc40389cd5d340a9e3b17a81196ad0af64c3c4460812a87f836c7d5c0ce8a; original global index 5044.
def localCycle00099 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 18 2, .gapLower 6 3, .triangle 11 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 438f8db23e701f5e80df116b27be954f0a1826da39b715bd595b12082398c8b1; original global index 5224.
def localCycle00100 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 447838a91e5ea9b4fd7d92d3dac70299bc40c8c41002078d50f8ae4df28cd6cc; original global index 5298.
def localCycle00101 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 18 1, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 454266f25e90e8da6e5ef0ddf003a2cf02299f6a09439cccf7aba4f9d9ae5a96; original global index 5357.
def localCycle00102 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle 45a2eea63169f786eafeec5cd0a59451eb77eeca2604f416dd2bfdb79707ae20; original global index 5386.
def localCycle00103 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 3, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 460fd9d1d731eab3a74dd77dfe4211a1637aa8ba6ab8609bba8f001bcfa02b8f; original global index 5421.
def localCycle00104 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 46c0427a1c2c8cb82e7947c9186fe27960323fb190d5d8a1ac4498792f1b6e8d; original global index 5482.
def localCycle00105 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 4701d1c80c54cc3779cde420c829b8e026909bfa7c3d75c921b8c89f18c1ae31; original global index 5502.
def localCycle00106 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 25 0, .triangle 26 0, .corridorLower 3 5]

-- Original cycle 47fdb967e87c30205bcefe54a6803d4c8c75e387c3f3a9322b8062c78dca9773; original global index 5572.
def localCycle00107 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 3, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 2, .triangle 21 0, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 486f0b749b2b5363a07f4416413d7147c1da06be7269dce19b6334a806cc70e4; original global index 5608.
def localCycle00108 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 2 6, .distance 1 6, .distance 5 6, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 24 1, .triangle 33 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 4a478674755cd4bb49888d1f9aaefea15659ebf778d8cee69208efab0cc46d8c; original global index 5763.
def localCycle00109 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .triangle 17 1, .triangle 15 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 4b3c26557c0a8b022606e692b8d98b2eb0dc08ecb18fedac49629b28a53aeb0f; original global index 5834.
def localCycle00110 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 2, .gapLower 6 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 4c510d585f8bb6e39c028da7b89f5afca4c7e5857268d82be2ca5eb7a9168bf9; original global index 5924.
def localCycle00111 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 4, .triangle 18 1, .triangle 17 0, .triangle 26 1, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 4cf0c6b28d77e248570e2372f100bd8098d8fb4d3d8154cc9d23c89137d48aa9; original global index 5975.
def localCycle00112 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 4de2fe757c1a1f62a287682ebc03ae54c489041276d10211652dfb449ff144ee; original global index 6045.
def localCycle00113 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 21 1, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 4e6d936567c0eca52a4b33f68b4607304fba71b041bc4673aad2d0b30a108422; original global index 6090.
def localCycle00114 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 51260c85946f28b9d88479db4c5ac577822a9b10b0024b8e908eb65b567d8fae; original global index 6305.
def localCycle00115 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 52714bf0041e695b57ef7b1726a79d5ef92b4e265d4509f9fc21cd0efeed4b6e; original global index 6410.
def localCycle00116 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -3, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 21 1, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 52b8c2834448990b8b7f9aa1e139e3c36768b620bf2b46735d05ea675c87a6b0; original global index 6433.
def localCycle00117 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 2 6, .distance 1 2]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 18 2, .gapLower 6 4, .gapUpper 2 3]

-- Original cycle 5378161960b7118c45e75bc684c41d1703aeb4a84e699ecea74daf440f51ffa8; original global index 6487.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 537968478e0d5a552b7dba92d5b15b4168a80b0b5970c48da21f57835b8bdd1b; original global index 6488.
def localCycle00119 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 5 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 14 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 571d3476651ec09c5595fdbec26fd86fb76873b48aef96368df451950876cf87; original global index 6750.
def localCycle00120 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 581a80d99d839b9f66ff25d08e531a60be0668f5fd5819aadb0b6431c8212494; original global index 6836.
def localCycle00121 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 584b1cfb2b4c5724a35144e60e9281b6658fcb262aaee651f7610534fe89c464; original global index 6852.
def localCycle00122 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle 59a2f81fd646c6241e885db3e54b05ee98a925bc2fa215392991a06d9c76a82f; original global index 6970.
def localCycle00123 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 24 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 5aa02169559f8cd321b444c8265e669913eaffab401bd95c68862c3c6c31fa80; original global index 7054.
def localCycle00124 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 24 0, .gapLower 6 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5aafa80ca9b4379707c30a27f2adf5617cea0dbaf7c242f3ce5b9c7358e17a34; original global index 7061.
def localCycle00125 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 3, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![4, -1, 0, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 0, .triangle 15 2, .triangle 21 0, .triangle 11 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 5bdf9d10b2f013a1b1e8855466ca2b5b9ded02f7528a4763c8f45e160e114901; original global index 7143.
def localCycle00126 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 5be6dfe64b719b6b1ba3f117088e6a1a8b58153e41f08e7299da5363876cec1f; original global index 7146.
def localCycle00127 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 5c3ecec023570ace9d4fcd7651d844cef3148c3450d8dbe99a0ceda6460f1154; original global index 7182.
def localCycle00128 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 2, .gapLower 6 2, .triangle 14 1]

-- Original cycle 5e09285a1c9ef41a3d37c566ce7d33727c9b926236d42505e4d08d31e0aadafb; original global index 7312.
def localCycle00129 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 2, .gapLower 6 5, .triangle 18 2, .triangle 24 1, .triangle 34 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5fb898da796f23b6eff4ec20b28523296c6f32508a186d012968f505d1a3b6a2; original global index 7457.
def localCycle00130 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 5fcf7edf83f0edeedb0b2e017f2eb57ca1255cd465e44f0d9aa09b6e53f561f6; original global index 7469.
def localCycle00131 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 4 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 616513a0de667fe838569324ecc18312aaf37e4f69629e07dc967bd00f6d8d4c; original global index 7596.
def localCycle00132 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 61733db81fe8a2780bc78b178f804049b57b089a669eb93525ae73634740ebcd; original global index 7599.
def localCycle00133 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 18 0]

-- Original cycle 6183ad74dc2c9368468d473fe80d084b0b2435ba86db0a6e7c285d8533f080d5; original global index 7606.
def localCycle00134 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 32 0, .triangle 13 0, .triangle 12 2, .triangle 10 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 65acb5752a3809c7588d7979177cf6a18cae8a397b1b32dbdd0fee773e1c05c1; original global index 7908.
def localCycle00135 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 66a80c507cfbc941fbb8ca04b9ac579a2e979793cd0475aa4931fc17d2f1ff5f; original global index 7979.
def localCycle00136 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 2 5, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 7 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 66ad46e74633233b123c2154f90d9129861544c2471a675c685c423ddeb050d5; original global index 7981.
def localCycle00137 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 6748bce8daa94abb640eee75cca2afbda9cee46823013be8427a3baef760b6b0; original global index 8031.
def localCycle00138 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 67c60bc86b977064d40553943407ed2684b44bca57c0fa04096afe865089bf9c; original global index 8062.
def localCycle00139 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 2 6, .distance 1 2]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 18 2, .gapLower 6 3, .gapUpper 2 4]

-- Original cycle 681d9618752471661c432b9e0a06e55744f63b8a4e30c092252355b83d5ed165; original global index 8091.
def localCycle00140 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, 0, -2, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 5, .gapLower 6 4, .triangle 33 0, .corridorLower 3 5]

-- Original cycle 68806b2fcbc188137a5668e0430d24e2c41b6bc537373d575dc54b636088849a; original global index 8128.
def localCycle00141 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 2 6, .distance 1 6, .distance 5 6, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 18 2, .gapLower 6 4, .triangle 33 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 69580338fb722790b592a216bbd60b61318057f71594034966f9304418f444b9; original global index 8196.
def localCycle00142 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 5 6, .distance 1 5, .distance 1 2]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .triangle 24 0, .gapLower 1 2]

-- Original cycle 698af1f02b84b8a00977e8b2db6cfa0a5d54747e3ac2869874f997c9fceba94f; original global index 8207.
def localCycle00143 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle 6a281382ef66a019f0b0b670a4dfe0ddc94c4ef49197c9fbc618cabd0821cabf; original global index 8257.
def localCycle00144 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .triangle 11 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 6a4c08cfd1690c503cab8990a3e91330d81ad606f34133a02ac8ad6861e50279; original global index 8277.
def localCycle00145 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 11 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 6a57f3fdfa27af23a704dcf7b63dc1d9af1693e49fc705caaf7859f6a6a984e3; original global index 8280.
def localCycle00146 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle 6ade187232a4e09d09432243bd3934d5ee2a9c605e7996bbf1faef37cdd20f82; original global index 8321.
def localCycle00147 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .gapLower 4 0, .thetaNext 3]

-- Original cycle 6b89bf85743496e7b9e25fc7346b2e7c6908c8d398cd6b0c9340b8ea14b1498b; original global index 8372.
def localCycle00148 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .triangle 21 1, .triangle 20 0, .triangle 26 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 6c391815c55848496a8f69b871c3de0aa523d50e667af091eae5be6b6890205d; original global index 8430.
def localCycle00149 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 6c52e8b35653e2608f7c5a7067ea69774d1f2198d445956673f994666b89604c; original global index 8439.
def localCycle00150 : Cycle where
  length := 5
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle 6d0b9dc6fa0ceae3ac34bd0a743b53f6b5fce6bef4fed90b3307ec06d26d55dc; original global index 8481.
def localCycle00151 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 3, .triangle 21 1, .triangle 20 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 6d63bad613404ae0eedfde32fe5aa03b6989e1fc04d60654c368b1fbf479db60; original global index 8504.
def localCycle00152 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 3 6, .distance 0 6, .distance 0 3, .theta 3]
    constant := ![3, 0, 0, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 2, .gapLower 6 3, .gapLower 6 2, .triangle 11 1, .gapLower 3 0]

-- Original cycle 6f07abf71490ebd876dd0219841890d8a98fc9302991703ec07f6080e8c26a22; original global index 8611.
def localCycle00153 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 71336dace226f43f01607bf54e373e3afa2977f2301be7a0bca5333a441b840a; original global index 8779.
def localCycle00154 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 2, .gapLower 6 4, .triangle 11 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle 715f11c5d723ac8d7bbf36ef2b4c9828db7e72b63a5d7a04bf4d8ce2462de88c; original global index 8794.
def localCycle00155 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 2, .triangle 18 2, .triangle 4 2, .gapLower 6 1, .gapLower 6 0]

-- Original cycle 7184847694214a045982e0a34ae81e302b62707976af776f036e7d5f7aa48c34; original global index 8810.
def localCycle00156 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 723acd66ecf6c25140988422753afa5a35f19ffc380f2fba051e623866a477d4; original global index 8856.
def localCycle00157 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -1, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 72c34dfe2d5af3732e917553b50c36b9a6e43ce2262ff3254e539410047e35fd; original global index 8886.
def localCycle00158 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 73510f3f7151d630fe3f1b4e1e3334d20a7accb694658a8f09be7cd4ce7b3ae8; original global index 8926.
def localCycle00159 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 7358761916c79cc60f23d23a9a5fd97c5731c5996a40a509fb8275ba6a2e0b8d; original global index 8930.
def localCycle00160 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 2, .triangle 18 2, .gapLower 6 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle 73847055569961743fca793c3611c82b683b7b38e6097fe23e21ae18162db432; original global index 8955.
def localCycle00161 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 5, .triangle 24 1, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle 7392e48ac379b717e22a0a4c14245ffc9a0da2fb0be67cb23ddb88ca0a48293f; original global index 8961.
def localCycle00162 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 73a58064fa33c28ffe4857221d49b95f1b0e8ebcffb13db1bd7582615f55c602; original global index 8966.
def localCycle00163 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 74a9fd0540e5a758ade55e806e60309d9c491f2b6f8ad6e860cc92979a580c80; original global index 9037.
def localCycle00164 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 29 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 766a00fb5fd6ac5fa3167b3d48da9af206e777e1aab63c32dac4628450359888; original global index 9167.
def localCycle00165 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 76a9038bf60461c7ae5d7d927109b3743256acef037b92421b04ecf2ef142bff; original global index 9185.
def localCycle00166 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 3 6, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 3, .gapLower 6 3, .triangle 33 1]

-- Original cycle 76c20cacb30145dc8c9658833df341d0e67c04c82e23392e31664853025e0688; original global index 9190.
def localCycle00167 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 771df14ccb996ff90a033450d6c3d7eabb8992c939dee98a691bb767b5073a71; original global index 9221.
def localCycle00168 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 3 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .triangle 21 0, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 786443ac4d72ca66a82b740009e0d9500b87f7c6bff7ef0f04e34293d061d853; original global index 9309.
def localCycle00169 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 32 1, .triangle 25 0, .triangle 26 0, .corridorLower 3 5]

-- Original cycle 787cd7b6a90e69d7b44877d614c03c7c51782ee83991c9700294edca57f1d6c2; original global index 9320.
def localCycle00170 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 78c435ff5fd5b6aef853ef066f0b63821a0ce2da3be75521afab1d5e3e4473e6; original global index 9345.
def localCycle00171 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 7a2fb8571a9ac4213012632186390cf8d5a35fa5548ad92b7bf9db6bef06cfda; original global index 9449.
def localCycle00172 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 3 6, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 2, .gapLower 6 3, .triangle 11 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 7b091117f0a2f15b770a0bd87ce68c36c7964bab020c6a79cc43f8f73f041390; original global index 9528.
def localCycle00173 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 1 6, .distance 1 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 3, .gapLower 6 3, .triangle 24 1]

-- Original cycle 7b7fb8ff4088cba9130a80a0c92e5cc259eaba31d0a79f5b0835b1c61291dff1; original global index 9558.
def localCycle00174 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 7c106aa792b3a97ecc8f6983768366541046b39fc8ff0a8a1fb8a04dbfd6cb2e; original global index 9596.
def localCycle00175 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 3, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 2, .triangle 21 0, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 7c201a7e87a92da3584078ea1cacc7660ee0371f4b8cf000ec37f0667fbb5be5; original global index 9603.
def localCycle00176 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 7c6e1a224062d865f5cf17b02b6c5d447345b41d506279c5501ad73bb7ef08c7; original global index 9629.
def localCycle00177 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 5 6, .distance 1 6, .distance 1 2]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .gapLower 6 4, .triangle 18 1]

-- Original cycle 7cbeb1ed40fb5519be8720fae5946fb402af0ff4f1f09e6576d3deb857217d5f; original global index 9659.
def localCycle00178 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 3, .theta 3]
    constant := ![3, -1, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .gapLower 6 3, .triangle 4 2, .triangle 11 1, .gapLower 3 0]

-- Original cycle 7cc36b9f69fa4d92918a935aa3665e2358713973c785006832f9496e58dc2414; original global index 9663.
def localCycle00179 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 4 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 7d78f391f79b6ad01442b844b3f2feb782d02b25da15dfd8a0b003f611d3e993; original global index 9732.
def localCycle00180 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 6, .distance 1 3]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .triangle 21 1]

-- Original cycle 7ec29b9ab698c01a5083363025387ae1b9233dd834534450c0400466a1f681d6; original global index 9845.
def localCycle00181 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 7f5254db735348cbfe6093fc849c9e057a5709ff4331d98a3117fe2a7d971fba; original global index 9873.
def localCycle00182 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 18 0]

-- Original cycle 7f57a0c36d16fbdf9733389a42cd3229b26731a62bc57a95e364bea16056abd6; original global index 9874.
def localCycle00183 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 24 0, .triangle 34 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 7fa314d096f4a2fc412c4312edb9ceba00ad62471bdab4d07d83ab0c66a6294d; original global index 9900.
def localCycle00184 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .gapLower 6 4, .triangle 24 0, .triangle 20 1, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 803a12a903f0c8e4f4d7514bd1b2f3419e2c154a3b7703f1198dc2312413d113; original global index 9947.
def localCycle00185 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 807f58b206ce8ec43f85b81ef7c34eeb97d75f41c0b0fbfa03ef3926dc837d35; original global index 9973.
def localCycle00186 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 0, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 80fb0a2a24859ca520d57a74f9a245e2630b61c94093386a384d3fc4e421e1ea; original global index 10010.
def localCycle00187 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 81594283736110a1e8fb799611a31c41864de4ce60e802c02ecaa0d806290257; original global index 10047.
def localCycle00188 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 82126c5cb9c27aac91d9af65a58226a039556dbb65df050b00b55ae78c26df30; original global index 10099.
def localCycle00189 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 6 4, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 8388f1a90e54f9ddba63829ff0f034d3e3452e85c30ecb5a1d81e007ce34e40d; original global index 10207.
def localCycle00190 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .theta 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, 3, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 29 1, .gapLower 6 0, .corridorUpper 5 6, .gapLower 6 5, .triangle 21 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 83dc5df33c762aad5489c04620d74f68eeb414b80d84886ee7f4075d475bdfb3; original global index 10235.
def localCycle00191 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 84461a5f6ffdefc34313f300757cc5586698c975e26464456bb2a6409681013d; original global index 10272.
def localCycle00192 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Original cycle 8451e85fadb4962ecd0e8200aad695e176e8c3d98209e235b1d0e5f9611034a5; original global index 10279.
def localCycle00193 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 21 2, .gapLower 6 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 859201210afdc5e49f95bc0985f1611f0425d125331929db9d6938763c42096e; original global index 10366.
def localCycle00194 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 21 1, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 8604cf705b5f34a506fe383518c4414a160d1fe5427b48382bfd59266d48a708; original global index 10396.
def localCycle00195 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 892438758687eed8b3485b6f2c098406c2b52f0ec02a1055fe08546e8b6e1a04; original global index 10613.
def localCycle00196 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 1 6, .distance 1 2]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .triangle 18 1]

-- Original cycle 8a89a97a51beb062890cb94daa205184d1eb00dc59a0a10ec636bba31961b5c6; original global index 10731.
def localCycle00197 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 4, .gapUpper 5 4]

-- Original cycle 8af064062950a6aa60e34dba2f74fbc59c6b0b85f147e3e59649c5e447dd9484; original global index 10769.
def localCycle00198 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 1 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .triangle 21 1, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 8bccdd9676d79a22d0d121d78d11e98869cb59af738d030c0e1158abc2b55a27; original global index 10825.
def localCycle00199 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .gapLower 6 3, .triangle 4 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 8d345090e2552254cba0335d356556f2317f9de7bfac630df75438a01d4e421e; original global index 10917.
def localCycle00200 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 18 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 8ddb1d984ba3699c2952f9b0dada42ee539d097a2ba31477b24057e99a34e512; original global index 10981.
def localCycle00201 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 8df43826af6a453985eb71754cc6ad6136aa01b472d78a33792e345435faee0d; original global index 10991.
def localCycle00202 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 8f6925c99a05d91199c1cdf7390bbec74334b642ea7ee83baf616735d4b1a1d8; original global index 11098.
def localCycle00203 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 2, .triangle 11 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 8ff35206b76948545dfd3423fd840bd9d0357a2580a0174eea9ae748d6c3ed3b; original global index 11144.
def localCycle00204 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 92037d1e2a7cdc09edf74aafa11a1392155701fee053a68220adf9c67de1a3d8; original global index 11315.
def localCycle00205 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 92ce83c9da10931539fab072f921e861b4de0fc9c4b2e30d22e39d4895c380de; original global index 11377.
def localCycle00206 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 0, .triangle 17 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 935eaeb414d65cfd77a988f439947ba6367e6a4768a9e25b7e26726211712e47; original global index 11429.
def localCycle00207 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 1 6, .distance 1 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 24 1]

-- Original cycle 93aae4dd5e297271314f283d634918de8b839c123dbf3797629d80c1dd7d0305; original global index 11456.
def localCycle00208 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .gapLower 6 4, .triangle 18 1, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 93b800aebdf62f62897ec4c87fff4de60fca13f08778241b882b24c642c173fe; original global index 11461.
def localCycle00209 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 9402900322bbc6536aeac733f4f03495a888f641f3001ba5896cc3a315ab23c4; original global index 11479.
def localCycle00210 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 2 3]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 2 3, .gapUpper 5 5, .gapLower 6 5, .triangle 27 0]

-- Original cycle 94551ace336cd300562e014f30087dae6f4f15436053cad18190cfc146a33b1e; original global index 11509.
def localCycle00211 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.gapUpper 1 1, .triangle 20 1, .triangle 26 0, .triangle 5 0, .triangle 0 1]

-- Original cycle 9473f7231272a14fc30da34332344ce4d4030a4fc33359f0c707bd4b86fd6156; original global index 11521.
def localCycle00212 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 96272aa77eed0942f54f1dfbdc705ebe3a6ab7506f8493d4c8bd60f0863d909c; original global index 11672.
def localCycle00213 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 6, .distance 0 3, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .gapLower 6 2, .triangle 11 1, .gapLower 3 0]

-- Original cycle 973d196ce4cae0a238a7de1adb2afc18b1ef9ccd73e3397cca54f5f7e5038c5b; original global index 11752.
def localCycle00214 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 4 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle 978bc187b5ffdcf7392c86de417308aa3db36b43cf92be9a4ee74dfef63bff62; original global index 11774.
def localCycle00215 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 29 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 97996238a5dcff1f1a654f573608ab2291fe10122ecbddd7ddccc62cb02f4d67; original global index 11775.
def localCycle00216 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 97ece87445c15ead48a72a9cc43ea966be2bb91555ab6e31c9a1560ab6844b97; original global index 11798.
def localCycle00217 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 9815778812a97cc6562d90a84df1d9a6a8fb43c5006a9a649bbbe643b59c5ade; original global index 11813.
def localCycle00218 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 0, .triangle 32 1, .gapLower 4 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 9aea766ea46438fb184f5ad9b99d2298a3677f5dc70065ca277bb930b4bdebc0; original global index 12039.
def localCycle00219 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 8 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 9d43067b6667c4607d89fe13c7fb194019e3177662a24c9a0683f1fa86718ec0; original global index 12234.
def localCycle00220 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 9e8007d3690c562cffe74d19d0bb80f267b904403678e6cf6f4cf858c48e842f; original global index 12344.
def localCycle00221 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 9edf8eece35d6b5af3352815b711a783326a24ccfeb8b56bfcf6c56226d19d72; original global index 12367.
def localCycle00222 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 32 0, .triangle 29 0, .gapLower 2 3, .triangle 26 0, .corridorLower 3 5]

-- Original cycle 9f95f3c05496bd2aa8624465d0f9979868ab376f6f9a8f859b0c9ce58a6b1f77; original global index 12419.
def localCycle00223 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle a033f8a15887b02aeeb32e588ae184ed7e175ea6b522568b46f56d14f2042063; original global index 12462.
def localCycle00224 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 11 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle a0444641fbfcccb3bf2fec6664fe72526118513318f8d1e7d16433555156fe2e; original global index 12470.
def localCycle00225 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 0, .triangle 34 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle a053f2d5b6c282a8ff8986d1179f96779d887c8c2b5a5a086d04810072e9a40f; original global index 12476.
def localCycle00226 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle a143b595e06980b402e55303830f5b41753078fa9bd03bfaed83c1404a2d72de; original global index 12540.
def localCycle00227 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 0, .triangle 3 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle a22982c8ca3f1e92542c8ca25a353abcbdefe46dc3e5d2e54e1fdfbd76fcab85; original global index 12617.
def localCycle00228 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 32 0, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle a32d7caa081b444173ae0cd45bb29cff48e5497f8f585967c416751c58bf7819; original global index 12685.
def localCycle00229 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .gapLower 6 4, .triangle 24 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaLower 3]

-- Original cycle a44981bccf878c8a259a6c0f66871d73585d2793ba20bbbe93f9a6174464db2b; original global index 12768.
def localCycle00230 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 2 5]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 30 1]

-- Original cycle a49a6547646105f05e91ca6354f5ae4785e9988b4b6e34d4bfcab5014cefed6e; original global index 12794.
def localCycle00231 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 5, .triangle 30 0, .triangle 24 2, .gapLower 6 3, .triangle 11 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle a5a81a84bd2c5594e15600266c963fb47376310f9c8753633919245f4ed09c8d; original global index 12868.
def localCycle00232 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .triangle 21 2, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle a5ad8fa92a6bf9e10cc9262dfbcfb7513602b1c80084e764fef570449ea33a42; original global index 12872.
def localCycle00233 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 4 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle a5ddb9888a0f768029787c9ff013de94b4e16dd11631c62d310903ea7b6aad0c; original global index 12884.
def localCycle00234 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 5 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle a69bbcc846662388dd9fda17a6c94ad8406bf26c72bb487d258906b569206f4e; original global index 12943.
def localCycle00235 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 11 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle a789cd799e9df3edd103a8bcea756d10ac4a903005fa8539874e5435a1e2134c; original global index 13035.
def localCycle00236 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -2, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 32 1, .gapLower 6 0, .gapLower 6 6, .triangle 30 0, .triangle 17 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle a7cb37a65579ca5cb4c26e640e375c61a04780ad150f080f6aa2b30bc292568d; original global index 13055.
def localCycle00237 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 21 0, .gapLower 1 3, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle a8e299cdabe3de76be9045e0273ba621e7885aeb35149d4072f62884559f972b; original global index 13148.
def localCycle00238 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 3 6, .distance 1 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 21 2, .gapLower 6 3, .gapUpper 3 3]

-- Original cycle a97010ca64e3bedbc022edcd0a519743fff5df5d855b77adc24d77c89c2c934f; original global index 13189.
def localCycle00239 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 2, .triangle 11 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle a9707215f99a8e69d5fcd6ef958d61def534f35a301e1e20c240afc21aadd29c; original global index 13190.
def localCycle00240 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 3 6, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 33 1]

-- Original cycle aa1ae171ab421f22bf82717b30d5e1c3c6a639091cc8cf58bc00c6f3bf5646d3; original global index 13245.
def localCycle00241 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 11 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle ab55ebb62537ecc2b07eae0320fc4515d2e80aa8a1760ce5145427c59717d406; original global index 13350.
def localCycle00242 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 5, .triangle 17 2, .triangle 24 0, .triangle 33 2, .triangle 11 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle ac0ed5e1a42c67c1d50c9a8122a559277fa42cc41621bc62b541acbe63296fd9; original global index 13410.
def localCycle00243 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .gapLower 6 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle ac6ed01f60b8c0d727775c8346b3169a5dec02be6fe411091f3fcf0d963ffba6; original global index 13440.
def localCycle00244 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 21 2, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle ad2392098cc075a2528f13a6f4687e629b9acd91e3d2689d191f3320552a7f44; original global index 13496.
def localCycle00245 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle ad56fdddb7ff7da7181b8d694227ddf0e6bba43497a7a95d6cbcce6aea1cb79f; original global index 13517.
def localCycle00246 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 3, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 2, .triangle 21 0, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .gapLower 4 0]

-- Original cycle ad835e597f5358cba9d2faa6c0fbbb484fdd7bd86d87576290731982791dd053; original global index 13536.
def localCycle00247 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle af80b9228b17629cab283e0a4c1c8195569772000a2034e95203dd226ffd6e52; original global index 13705.
def localCycle00248 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle b021ad4ff761e54acf0036e2ed7f8d25236c2f7696e46924cd468915ffa2265c; original global index 13752.
def localCycle00249 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 18 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle b0a65d5ec74dc3d83775ae3456745dfc09969d4a1dace3929e4ec8d8240e7787; original global index 13793.
def localCycle00250 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 20 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle b0fb39ba05bd11aa077c82170efdcf9981778d4db6dcbad6ce928ab5cbebfbba; original global index 13816.
def localCycle00251 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 8 2, .gapLower 6 1, .corridorLower 4 6, .thetaLower 4]

-- Original cycle b1196f64d4e92440d2b61630d26bf7d448da3ac6ab5ee548ee6d89fe4cb80d2e; original global index 13828.
def localCycle00252 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 5 6, .distance 2 6, .distance 3 6, .distance 1 3, .distance 1 2]
    constant := ![2, 2, -2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.gapUpper 2 2, .gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 21 0, .gapLower 1 2]

-- Original cycle b2e69afa3b2c346a1624f9975c4c90defcf7f515c7ab0f90eb0fea19b86bc55d; original global index 13983.
def localCycle00253 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 30 0, .triangle 7 2, .triangle 12 1, .corridorLower 4 5]

-- Original cycle b48ac9544d592871c6c3486c3f108d71be69524578a6bbd48e1e0fa461c3868d; original global index 14100.
def localCycle00254 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle b4c79241f7d9b02483833573302750024b1184619ef49e06bd0f2393fce91f4c; original global index 14116.
def localCycle00255 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 24 1, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle b5de2abe9e6c1b139b645bc12abff46c1a74757d051b3b1d86bf96a7122e6162; original global index 14210.
def localCycle00256 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -3, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 24 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle b725b7a7b3beac495a61126c221e745e9cfa6d6d2ed798bb2ae3976a4ab01035; original global index 14302.
def localCycle00257 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 5, .triangle 30 0, .triangle 33 2, .triangle 11 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle b8a5bd1f51cb8a2db215aeee83d819cea7ae377ed8a4885b82268d20fdd5e3f8; original global index 14410.
def localCycle00258 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 4, .distance 4 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 2, .triangle 2 2, .triangle 13 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle b94fb0559ebd2dd2857f868638b86bd1bf48d906321ab055725a6c34ef98c9eb; original global index 14459.
def localCycle00259 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 2 6, .distance 1 2]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 18 2, .gapLower 6 4, .gapUpper 2 3]

-- Original cycle b95ecb5e3d9f7c923e8f0a988d664dacfc79fdc5e110f0e54252acd2c03bce79; original global index 14464.
def localCycle00260 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 2 6, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 30 1]

-- Original cycle ba52e68e960509798d176200f9db321ac4ab272430082b46cba8a6e17a166721; original global index 14549.
def localCycle00261 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle bb110969772848596f716a446c1a137d7da94abeb946db61f8bfb30872948dcb; original global index 14609.
def localCycle00262 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 0, .gapLower 6 4, .triangle 4 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle bbbb5e6e397aeb2358d49010b6d1f325f2875a8f09e864fea643baaaa6acd8b6; original global index 14660.
def localCycle00263 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle bc9c01e799a9ce50e99854338cd70a0570f72342f2d4caee95a122a69e255d59; original global index 14711.
def localCycle00264 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 0, .triangle 18 0, .triangle 27 1, .triangle 11 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle bce286f1392effab3cd1493fc0d1b54a53966871684a2c77d8497f8ebd5f228f; original global index 14735.
def localCycle00265 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle bd4480434fcd8e3af043d562c7e7eea2dcc80ee4d59dfc4fe7c25ff02ae9154c; original global index 14762.
def localCycle00266 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 4, .triangle 4 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle bd7e9656b5159af002e0b04971df3863b0745475f2cf91e7fb82e4424a9c9ffc; original global index 14781.
def localCycle00267 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 1 6, .distance 1 2]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 4, .gapLower 6 3, .triangle 18 1]

-- Original cycle bda659af50738dd02e9c9d1aba13fca736a95df92a8627a6a5ddac35cdd5af42; original global index 14794.
def localCycle00268 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle bde254f910100be3cd97220f616bd1ef681b88e2f16e55a1308ba811c7a8d6d6; original global index 14809.
def localCycle00269 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 6, .distance 0 3, .theta 3]
    constant := ![3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .gapLower 6 3, .gapLower 6 2, .triangle 11 1, .gapLower 3 0]

-- Original cycle be2e05b88d78c89f807a5300f108969b20ec3c20c4078bf4bf4ab8bc62809514; original global index 14834.
def localCycle00270 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 2 6, .distance 1 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, 0, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 18 2, .triangle 24 1, .triangle 33 0, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle bee69768af5ab2eaceca05df1b7c09ad60947196b25e76eb2d8420dc666a4c8c; original global index 14893.
def localCycle00271 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 24 0, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle bfb2c5e4ebdb703ae12b3298e5fc0de198de41a38296bafefea0a88d3f96d072; original global index 14953.
def localCycle00272 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle c17fa70913583786052ca41d6b21a1f133b698737c79ac03c32a808d059e6aff; original global index 15113.
def localCycle00273 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 11 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle c2606bebbe346d46f66360e3c9ee272594c3094d1bc8485a7aa0041cffa84159; original global index 15175.
def localCycle00274 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 3, .gapUpper 5 3]

-- Original cycle c362517fc8da9c757901e950c265a553902cf6b99a3967293680556318d84cb5; original global index 15244.
def localCycle00275 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle c50a3df63e987e4b92f9f3ae62682497b45689eaa86a55730da5d961066fff4c; original global index 15375.
def localCycle00276 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle c5e14b73659d58da81bf5b4e521702f353e2b1afc31d69c32866b84e9a7a0ecd; original global index 15430.
def localCycle00277 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 0, .triangle 24 2, .gapLower 6 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle c73f8d3196269f6e49dfbca1d00fc41cc4e106b8afa56e6b8851b5b4ff11f8c1; original global index 15549.
def localCycle00278 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle c7ee013a7502bf2f19cf7c639e12dd86bf97d394e8025f018c70cd231d379c1d; original global index 15608.
def localCycle00279 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 24 0, .gapLower 1 2]

-- Original cycle c87e313d19505b6fe7d36083a6bfaaa113a8efd9693a5fa1aa551bb3f9455aaf; original global index 15658.
def localCycle00280 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![4, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 15 0, .triangle 18 0, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle c8b5b725c3248f97cc25d4e0f1210f35c1f9e79d7b1de10c4485a2cfc116c85a; original global index 15678.
def localCycle00281 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 5, .triangle 17 2, .triangle 24 0, .triangle 33 2, .gapLower 6 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle c90fc0410c2f6efcef5a6be97749d7dbd41f7c342cb612ca9e55436c75161b78; original global index 15703.
def localCycle00282 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 3 6, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .gapLower 6 3, .triangle 11 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle c923ac73aa78db1e92197ce53d0d8e4c0b0a94a449cbe8259bf5207f0656d5de; original global index 15714.
def localCycle00283 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .gapLower 6 4, .gapLower 6 3, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle c9bf7d8dbf567345b3530aa0c5ca7b5ba56da30fa9f6ff91648b6a4cad46cdd5; original global index 15772.
def localCycle00284 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 2 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 1, .triangle 33 0, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle ca907d6bc53aecbda65c5911627969c8db5523c351e68ce314ef5bdda107307e; original global index 15835.
def localCycle00285 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle cb23f75c23c830ba055b7c046d7e82fcf20de58c524b76707d64280643a7752b; original global index 15870.
def localCycle00286 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 33 1, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle cef79463d2c10edbf393dee0572cf11a1d243878dd174477685460d0e2237858; original global index 16149.
def localCycle00287 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 18 2, .gapLower 6 3, .triangle 11 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle cfab64ca5c223fe6d00cb33b88a667ba9277be2dc5f011097654ae3f0075728e; original global index 16206.
def localCycle00288 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle cfae6f01cf490c793b6ef09e30c815e216fc82786523453aa8f470fd7eafa120; original global index 16208.
def localCycle00289 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 7 2, .triangle 12 1, .corridorLower 4 5]

-- Original cycle cfb5bd7b52835638f9ced2508125dab2dacf30f87458ecfa4b6a93c9738b5560; original global index 16210.
def localCycle00290 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle d010ed373782cbc1662ea41831d01a8efc10908ca71cf12a8b73ea68cd850e55; original global index 16238.
def localCycle00291 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .gapLower 4 0]

-- Original cycle d10b5e974155c4b5b17c83c58c87654042e18568792212af6e4a691ad1376fad; original global index 16323.
def localCycle00292 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle d193eeeb519f158bd8d21c79011c764ddf5a16e9bc7e99ccb51841cf9ea064d9; original global index 16355.
def localCycle00293 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle d1b13e1b64db1b8394324bcfb3ee7c2a81721b7e09dc93c361bb8b2b95a34882; original global index 16367.
def localCycle00294 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .corridorLower 3 5]

-- Original cycle d26b9a21895436fe8709ae41350be2231b0a7d8453388d6ade5f94977240e0d1; original global index 16417.
def localCycle00295 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 5 6, .distance 1 5, .distance 1 2]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .triangle 24 0, .gapLower 1 2]

-- Original cycle d4df512587e12afc4469b531db4b1485cd64d8d97c3dd5002a8a6080c29b31ad; original global index 16608.
def localCycle00296 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 25 0, .triangle 31 2, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle d6bd0a924650da0127db804e4a4cd648b4dfd0bdbd684cbdac4e5835aabc5731; original global index 16764.
def localCycle00297 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, 0, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle d6ddd7d9ca95c224077abcc4df9c3c89b0670c8d36ceb66debbe1de6e6e3e422; original global index 16775.
def localCycle00298 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle d77aa6ac4353415e96f52f3f6818205ec79d9c331723f0c3df57675cdc550c94; original global index 16817.
def localCycle00299 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 11 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle da45d961ee821eb36ba290e8ed5667a2c86a5b32f954017e5ecde3828033b1c3; original global index 17052.
def localCycle00300 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 4, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle dab3bd1984676b366160e2d060d27d4c5998b4aa2a376ecdd1b3f6421449504c; original global index 17091.
def localCycle00301 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 1 6, .distance 2 6, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 30 1, .triangle 26 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle dafa6a2fe4e3ee2a34830f3658c2289edbc03360b3235d4da4d3ec50002b1801; original global index 17111.
def localCycle00302 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -1, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .triangle 24 0, .triangle 14 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle db48f34f240eebfa5e15a458f51a6974afc24ce47b858db4d24dc93c64ff1553; original global index 17140.
def localCycle00303 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 5, .triangle 30 0, .gapLower 6 4, .triangle 4 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle dccf3ad7b3ec20b4c0202af4d5154177c8b4a698d103ac89ac11404af0ac2789; original global index 17256.
def localCycle00304 : Cycle where
  length := 5
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 8 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle de5f761374a630e8403a02c90d440fd601768e629a2545dbfa0af8ee353a45a8; original global index 17384.
def localCycle00305 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 24 0, .gapLower 1 2]

-- Original cycle df5a127d59332ea5c15d531611adaa89f28a799cbd5919fe419d54f7f9a2ce7f; original global index 17452.
def localCycle00306 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 24 2, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle dfa5f5f67d13e8e3c6d7186b5c24af62e77a176da3f8a9c54b1170be91c7b5ec; original global index 17472.
def localCycle00307 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 0, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle e0247aa42d2abc65d22cdbfe0f8c232971b6797cb3282d5b42ea438737d3c642; original global index 17521.
def localCycle00308 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle e081cfc077928ddf68b78801f6b04a03ad255b7da46e362b6c7a7ba2db54b9f9; original global index 17556.
def localCycle00309 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle e17c8be99d5ee1a5014ea4ac79f10d7f7bf9f756778588b295f397cd0501917d; original global index 17634.
def localCycle00310 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle e2650ee67f69cdb056645f1641235249fcd84b76b4529a2d582e6557be293038; original global index 17701.
def localCycle00311 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 2, .gapLower 6 5, .triangle 8 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle e29f0a550b6e829bf60c25bf45f5fe5b48871ac4e0a15fa4a6eca9a6caadee54; original global index 17723.
def localCycle00312 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 3, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle e2c2dc82005be310c7666793eb02945af3efda547b7e95110dd6c40afa29d91d; original global index 17734.
def localCycle00313 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 2 3]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 2 3, .gapUpper 5 5, .gapLower 6 5, .triangle 27 0]

-- Original cycle e2f84fd79412f87a1894c5002bcaa192b95503758f3b99b02defcf3289d48b1a; original global index 17751.
def localCycle00314 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 29 1, .gapLower 6 0, .gapLower 6 6, .triangle 33 0, .triangle 20 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle e317dec798ba1162ca84bc8085c7a46987f7950e79026ba8319210c85791819f; original global index 17757.
def localCycle00315 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle e3bb372fcaef8247878717490c8f26bc94ed1f985ca2a550f0d269b1906481de; original global index 17808.
def localCycle00316 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 1 6, .distance 1 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 4, .gapLower 6 4, .triangle 24 1]

-- Original cycle e552319c1dcd7a01665ec4aab6697ee729802969074f6a83029ddfaa9af7d0d9; original global index 17928.
def localCycle00317 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -3, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle e5a52ff8bb22feaf69a6845b6806f71eeb7e9b2747a11476dbc145c806aad27e; original global index 17967.
def localCycle00318 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 3, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle e69d594c596277d209f7fc9ca28ebda4fe364e4bc92a196b2b26bd85d8ff2c88; original global index 18036.
def localCycle00319 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .gapLower 4 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle e743b5d74cd80a53a91d62e047310312b99c5b5954d365ff07f92fbd3ef6cb56; original global index 18090.
def localCycle00320 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 18 2, .gapLower 6 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle e7634757040ea3dafb57be737ace940e679d5f05e980c9927c74a8d29947168b; original global index 18098.
def localCycle00321 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .gapLower 6 3, .triangle 33 1, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle e890ee4802c3e25d533418bb84bd355139a6f5e1d302094f6886713cb88e6ced; original global index 18178.
def localCycle00322 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 6 3, .triangle 11 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle e9416b61b45c9cc6a921330440a2b2b5e801f6e17d381612d8936a7ffb008daa; original global index 18226.
def localCycle00323 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 26 1, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle e949aaeeff06c8bbb0c94850e2b3b2286e1ccf73e332ddf91e46a158e2a14321; original global index 18231.
def localCycle00324 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 8 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle e9d9813c1f18d09d05633ac2399e8976d9f34d6f2920237b2bfd74930cf0c387; original global index 18271.
def localCycle00325 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![4, 0, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 8 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle ead1253b291648f34d797674d4f7204149a843ba922f0edeef75c7710f4f0de4; original global index 18341.
def localCycle00326 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 6, .theta 6, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -2, 3, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 0, .gapLower 6 0, .corridorUpper 5 6, .gapLower 6 5, .triangle 18 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle ec105a3befe47335b4d75eacd97b18fe422a0f3bf40ca87db57bf38433dd8d64; original global index 18425.
def localCycle00327 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 4, .gapUpper 5 4]

-- Original cycle ecd3c3c73849ebe9bb9c87bf3d6ebdb943ed7c767c8eccb2d0cb5cd8cc3153e2; original global index 18487.
def localCycle00328 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 5, .triangle 30 2, .gapLower 6 5, .triangle 4 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle ed203cb8589e1a1de944b8cd44ec43518a0dae0f15fbaf378846f6a4ac22df18; original global index 18513.
def localCycle00329 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .triangle 18 2, .gapLower 6 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle edd96e5b0794afdf5ee98c3a0c7e6f4ab81e9cec26bb0749dec3522221f2929b; original global index 18570.
def localCycle00330 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle edda44a36eeeb5021fc525846677393bfd065acdb2a3e45c468ee3a80f1bd696; original global index 18571.
def localCycle00331 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 2, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle eecf9f7620bddd8f856a5bf7fd9f0c7337077ddfaf4db3f699a1ae0d987d15ee; original global index 18638.
def localCycle00332 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 21 2, .gapLower 6 3, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Original cycle eef12f8d126c68441bdc91416b8f498bb382b4dac22b39943369e8557083da86; original global index 18647.
def localCycle00333 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 1 5]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 24 1]

-- Original cycle ef1df5bef3a2d0c6a7f9eb6836fc7b698b2fa217c6759e6008c578a7995faee4; original global index 18657.
def localCycle00334 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle eff0852b1468b45482d2046fbc67ef1b4c76949dcf4143bf79174b8067780d46; original global index 18724.
def localCycle00335 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle f27cc3b84c6a21b148f55dfaa21e2e0cd824003fb14737e454a6bcfd4d53feb4; original global index 18907.
def localCycle00336 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle f2c10cf7ca4e99e49d5e7c1ed2165e4dfcb34e8f8207ce04eb9fcc76de935a15; original global index 18921.
def localCycle00337 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 3, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle f38131fddc328169f9778e5e4b9ecd6ba0ec0b2e189cf7da9639d77cfa78c5a8; original global index 18996.
def localCycle00338 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 18 0, .triangle 17 0, .triangle 7 2, .triangle 12 1, .corridorLower 4 5]

-- Original cycle f38599269ba814c3079717e25c565d881b641cfddc8802ad9b7f70b990d025ba; original global index 19000.
def localCycle00339 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 6 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle f3aeb5432a3d008c0833375a4621ae69726d1d4e9db36d86ed039e58047d1c8f; original global index 19010.
def localCycle00340 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 6 3, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle f47e9f4eb85d472a77bf5e83d6723b718b42755406497f7cfc13faebbc313b84; original global index 19063.
def localCycle00341 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .gapLower 6 3, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle f58a27ada69f5ea7eede536d8d756b243e51d75ee5ae4b6b9f6d368cb506c7da; original global index 19145.
def localCycle00342 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 2, .triangle 18 2, .gapLower 6 3, .triangle 11 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle f5e629243e486ccc4fe9a96d46c7eddcdfe10d01aec7cf4f9fc82822b6f11c93; original global index 19187.
def localCycle00343 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle f7c9c89a86f80a5024f097cf31ebd2f4066c1ef2c2b31f0c2d887d9a377a5012; original global index 19316.
def localCycle00344 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![2, 0, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true] }
  origin := ![.gapUpper 1 1, .triangle 24 1, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 5 0, .triangle 0 1]

-- Original cycle f81de02151433a7458427a2194d5ad5ae77fe8d2d8106de96bdc56004dbee75b; original global index 19346.
def localCycle00345 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 18 2, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle f84d7d1a67991d904bc96e6afdafc339fdcc93eed31aedbacd5a1d8e7bbf2bab; original global index 19368.
def localCycle00346 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 2 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 6 4, .triangle 27 1, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle f88547d1c6626baedce574bbd1019270fef82051a742a1a6d9f4ec952e96229c; original global index 19381.
def localCycle00347 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 6, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -2, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 0, .gapLower 6 0, .gapLower 6 6, .triangle 30 0, .triangle 17 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle f8ba2f6b7b0df870e34e709cd48bab7700d91d1d8510f653ba59c447db972b7c; original global index 19396.
def localCycle00348 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 0, .gapLower 4 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle f8cfd4e8f5ba2d13ac0c5aabbce3dd1403496ce965c11aab9a1dd95479e1fa6f; original global index 19407.
def localCycle00349 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle f8ff6805347261315bd8fe541be955420b9eb8443e00a338c88b72f2ea9aaa8a; original global index 19419.
def localCycle00350 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 1 6, .distance 1 2]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .triangle 18 1]

-- Original cycle f9c25c50890b7cb7bcb77293fa6e4224dc11e7fae3ebd85ca7992d2661050468; original global index 19476.
def localCycle00351 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle f9f75713f6531ded1525f28ef8399dee57f1869ea9b7a8d43f3891ddc013fd3d; original global index 19490.
def localCycle00352 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 6, .distance 0 3, .theta 3]
    constant := ![3, -1, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .gapLower 6 2, .triangle 11 1, .gapLower 3 0]

-- Original cycle fa812972843c03f49d61a94cb33d05550754b252756112ce6f84f059e5061209; original global index 19543.
def localCycle00353 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle fbbf8617dcc80eef79dd95002daccaeda8afc9b3ad61b9caa619119fcde651c2; original global index 19655.
def localCycle00354 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 6, .theta 6, .theta 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -2, 0, 3, 0, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 0, .gapLower 6 0, .thetaNext 5, .corridorUpper 2 5, .triangle 17 2, .triangle 24 2, .gapLower 6 4, .triangle 33 0, .corridorLower 3 5]

-- Original cycle fc2002a8e79135f2cf3bbe1b8095adc484bb97f3843ccc473b6f10d0ae266589; original global index 19687.
def localCycle00355 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle fca2a764d7545333b4355bc4a0cf904c3084868f7188c9bb7b064d0e9e7692e7; original global index 19736.
def localCycle00356 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -1, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle fca6947147f1ea645964c753b96d1f8f3f7c3a873a198645a92d80b6614b4dd1; original global index 19739.
def localCycle00357 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 5, .triangle 17 2, .triangle 24 0, .gapLower 6 3, .triangle 11 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle fd27e08055d43f3d0edf7e4965309d2e211c08528d493f6195d55f8b62f36382; original global index 19785.
def localCycle00358 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 2, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle fef47a891689ad5c12d346067a8dc5e9abb7aa82456abc734a28e0435dce06fe; original global index 19934.
def localCycle00359 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

def library : Library := fun id => if id < 180 then (if id < 90 then (if id < 45 then (if id < 22 then (if id < 11 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 8 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none))) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none))))) else (if id < 16 then (if id < 13 then (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none)) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none)))) else (if id < 19 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none))) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)))))) else (if id < 33 then (if id < 27 then (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)))) else (if id < 30 then (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))))) else (if id < 39 then (if id < 36 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none))) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)))) else (if id < 42 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))))))) else (if id < 67 then (if id < 56 then (if id < 50 then (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)))) else (if id < 53 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none))) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none))))) else (if id < 61 then (if id < 58 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none)))) else (if id < 64 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)))))) else (if id < 78 then (if id < 72 then (if id < 69 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)))) else (if id < 75 then (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none))) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))))) else (if id < 84 then (if id < 81 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none))) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)))) else (if id < 87 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none))) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)))))))) else (if id < 135 then (if id < 112 then (if id < 101 then (if id < 95 then (if id < 92 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)))) else (if id < 98 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none))) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))))) else (if id < 106 then (if id < 103 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)))) else (if id < 109 then (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none))) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none)))))) else (if id < 123 then (if id < 117 then (if id < 114 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)))) else (if id < 120 then (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none))) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none))))) else (if id < 129 then (if id < 126 then (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none))) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)))) else (if id < 132 then (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none))) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none))))))) else (if id < 157 then (if id < 146 then (if id < 140 then (if id < 137 then (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)))) else (if id < 143 then (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none))) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none))))) else (if id < 151 then (if id < 148 then (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none)) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)))) else (if id < 154 then (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none))) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none)))))) else (if id < 168 then (if id < 162 then (if id < 159 then (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none)) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none)))) else (if id < 165 then (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none))) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none))))) else (if id < 174 then (if id < 171 then (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none))) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id = 173 then some localCycle00173 else none)))) else (if id < 177 then (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none))) else (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none))))))))) else (if id < 270 then (if id < 225 then (if id < 202 then (if id < 191 then (if id < 185 then (if id < 182 then (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none)) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none)))) else (if id < 188 then (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id = 187 then some localCycle00187 else none))) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none))))) else (if id < 196 then (if id < 193 then (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none)) else (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none)))) else (if id < 199 then (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id = 198 then some localCycle00198 else none))) else (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none)))))) else (if id < 213 then (if id < 207 then (if id < 204 then (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id = 203 then some localCycle00203 else none)) else (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id = 206 then some localCycle00206 else none)))) else (if id < 210 then (if id < 208 then (if id = 207 then some localCycle00207 else none) else (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none))) else (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id = 212 then some localCycle00212 else none))))) else (if id < 219 then (if id < 216 then (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none))) else (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id = 218 then some localCycle00218 else none)))) else (if id < 222 then (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id = 221 then some localCycle00221 else none))) else (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id = 224 then some localCycle00224 else none))))))) else (if id < 247 then (if id < 236 then (if id < 230 then (if id < 227 then (if id < 226 then (if id = 225 then some localCycle00225 else none) else (if id = 226 then some localCycle00226 else none)) else (if id < 228 then (if id = 227 then some localCycle00227 else none) else (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id = 229 then some localCycle00229 else none)))) else (if id < 233 then (if id < 231 then (if id = 230 then some localCycle00230 else none) else (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id = 232 then some localCycle00232 else none))) else (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id < 235 then (if id = 234 then some localCycle00234 else none) else (if id = 235 then some localCycle00235 else none))))) else (if id < 241 then (if id < 238 then (if id < 237 then (if id = 236 then some localCycle00236 else none) else (if id = 237 then some localCycle00237 else none)) else (if id < 239 then (if id = 238 then some localCycle00238 else none) else (if id < 240 then (if id = 239 then some localCycle00239 else none) else (if id = 240 then some localCycle00240 else none)))) else (if id < 244 then (if id < 242 then (if id = 241 then some localCycle00241 else none) else (if id < 243 then (if id = 242 then some localCycle00242 else none) else (if id = 243 then some localCycle00243 else none))) else (if id < 245 then (if id = 244 then some localCycle00244 else none) else (if id < 246 then (if id = 245 then some localCycle00245 else none) else (if id = 246 then some localCycle00246 else none)))))) else (if id < 258 then (if id < 252 then (if id < 249 then (if id < 248 then (if id = 247 then some localCycle00247 else none) else (if id = 248 then some localCycle00248 else none)) else (if id < 250 then (if id = 249 then some localCycle00249 else none) else (if id < 251 then (if id = 250 then some localCycle00250 else none) else (if id = 251 then some localCycle00251 else none)))) else (if id < 255 then (if id < 253 then (if id = 252 then some localCycle00252 else none) else (if id < 254 then (if id = 253 then some localCycle00253 else none) else (if id = 254 then some localCycle00254 else none))) else (if id < 256 then (if id = 255 then some localCycle00255 else none) else (if id < 257 then (if id = 256 then some localCycle00256 else none) else (if id = 257 then some localCycle00257 else none))))) else (if id < 264 then (if id < 261 then (if id < 259 then (if id = 258 then some localCycle00258 else none) else (if id < 260 then (if id = 259 then some localCycle00259 else none) else (if id = 260 then some localCycle00260 else none))) else (if id < 262 then (if id = 261 then some localCycle00261 else none) else (if id < 263 then (if id = 262 then some localCycle00262 else none) else (if id = 263 then some localCycle00263 else none)))) else (if id < 267 then (if id < 265 then (if id = 264 then some localCycle00264 else none) else (if id < 266 then (if id = 265 then some localCycle00265 else none) else (if id = 266 then some localCycle00266 else none))) else (if id < 268 then (if id = 267 then some localCycle00267 else none) else (if id < 269 then (if id = 268 then some localCycle00268 else none) else (if id = 269 then some localCycle00269 else none)))))))) else (if id < 315 then (if id < 292 then (if id < 281 then (if id < 275 then (if id < 272 then (if id < 271 then (if id = 270 then some localCycle00270 else none) else (if id = 271 then some localCycle00271 else none)) else (if id < 273 then (if id = 272 then some localCycle00272 else none) else (if id < 274 then (if id = 273 then some localCycle00273 else none) else (if id = 274 then some localCycle00274 else none)))) else (if id < 278 then (if id < 276 then (if id = 275 then some localCycle00275 else none) else (if id < 277 then (if id = 276 then some localCycle00276 else none) else (if id = 277 then some localCycle00277 else none))) else (if id < 279 then (if id = 278 then some localCycle00278 else none) else (if id < 280 then (if id = 279 then some localCycle00279 else none) else (if id = 280 then some localCycle00280 else none))))) else (if id < 286 then (if id < 283 then (if id < 282 then (if id = 281 then some localCycle00281 else none) else (if id = 282 then some localCycle00282 else none)) else (if id < 284 then (if id = 283 then some localCycle00283 else none) else (if id < 285 then (if id = 284 then some localCycle00284 else none) else (if id = 285 then some localCycle00285 else none)))) else (if id < 289 then (if id < 287 then (if id = 286 then some localCycle00286 else none) else (if id < 288 then (if id = 287 then some localCycle00287 else none) else (if id = 288 then some localCycle00288 else none))) else (if id < 290 then (if id = 289 then some localCycle00289 else none) else (if id < 291 then (if id = 290 then some localCycle00290 else none) else (if id = 291 then some localCycle00291 else none)))))) else (if id < 303 then (if id < 297 then (if id < 294 then (if id < 293 then (if id = 292 then some localCycle00292 else none) else (if id = 293 then some localCycle00293 else none)) else (if id < 295 then (if id = 294 then some localCycle00294 else none) else (if id < 296 then (if id = 295 then some localCycle00295 else none) else (if id = 296 then some localCycle00296 else none)))) else (if id < 300 then (if id < 298 then (if id = 297 then some localCycle00297 else none) else (if id < 299 then (if id = 298 then some localCycle00298 else none) else (if id = 299 then some localCycle00299 else none))) else (if id < 301 then (if id = 300 then some localCycle00300 else none) else (if id < 302 then (if id = 301 then some localCycle00301 else none) else (if id = 302 then some localCycle00302 else none))))) else (if id < 309 then (if id < 306 then (if id < 304 then (if id = 303 then some localCycle00303 else none) else (if id < 305 then (if id = 304 then some localCycle00304 else none) else (if id = 305 then some localCycle00305 else none))) else (if id < 307 then (if id = 306 then some localCycle00306 else none) else (if id < 308 then (if id = 307 then some localCycle00307 else none) else (if id = 308 then some localCycle00308 else none)))) else (if id < 312 then (if id < 310 then (if id = 309 then some localCycle00309 else none) else (if id < 311 then (if id = 310 then some localCycle00310 else none) else (if id = 311 then some localCycle00311 else none))) else (if id < 313 then (if id = 312 then some localCycle00312 else none) else (if id < 314 then (if id = 313 then some localCycle00313 else none) else (if id = 314 then some localCycle00314 else none))))))) else (if id < 337 then (if id < 326 then (if id < 320 then (if id < 317 then (if id < 316 then (if id = 315 then some localCycle00315 else none) else (if id = 316 then some localCycle00316 else none)) else (if id < 318 then (if id = 317 then some localCycle00317 else none) else (if id < 319 then (if id = 318 then some localCycle00318 else none) else (if id = 319 then some localCycle00319 else none)))) else (if id < 323 then (if id < 321 then (if id = 320 then some localCycle00320 else none) else (if id < 322 then (if id = 321 then some localCycle00321 else none) else (if id = 322 then some localCycle00322 else none))) else (if id < 324 then (if id = 323 then some localCycle00323 else none) else (if id < 325 then (if id = 324 then some localCycle00324 else none) else (if id = 325 then some localCycle00325 else none))))) else (if id < 331 then (if id < 328 then (if id < 327 then (if id = 326 then some localCycle00326 else none) else (if id = 327 then some localCycle00327 else none)) else (if id < 329 then (if id = 328 then some localCycle00328 else none) else (if id < 330 then (if id = 329 then some localCycle00329 else none) else (if id = 330 then some localCycle00330 else none)))) else (if id < 334 then (if id < 332 then (if id = 331 then some localCycle00331 else none) else (if id < 333 then (if id = 332 then some localCycle00332 else none) else (if id = 333 then some localCycle00333 else none))) else (if id < 335 then (if id = 334 then some localCycle00334 else none) else (if id < 336 then (if id = 335 then some localCycle00335 else none) else (if id = 336 then some localCycle00336 else none)))))) else (if id < 348 then (if id < 342 then (if id < 339 then (if id < 338 then (if id = 337 then some localCycle00337 else none) else (if id = 338 then some localCycle00338 else none)) else (if id < 340 then (if id = 339 then some localCycle00339 else none) else (if id < 341 then (if id = 340 then some localCycle00340 else none) else (if id = 341 then some localCycle00341 else none)))) else (if id < 345 then (if id < 343 then (if id = 342 then some localCycle00342 else none) else (if id < 344 then (if id = 343 then some localCycle00343 else none) else (if id = 344 then some localCycle00344 else none))) else (if id < 346 then (if id = 345 then some localCycle00345 else none) else (if id < 347 then (if id = 346 then some localCycle00346 else none) else (if id = 347 then some localCycle00347 else none))))) else (if id < 354 then (if id < 351 then (if id < 349 then (if id = 348 then some localCycle00348 else none) else (if id < 350 then (if id = 349 then some localCycle00349 else none) else (if id = 350 then some localCycle00350 else none))) else (if id < 352 then (if id = 351 then some localCycle00351 else none) else (if id < 353 then (if id = 352 then some localCycle00352 else none) else (if id = 353 then some localCycle00353 else none)))) else (if id < 357 then (if id < 355 then (if id = 354 then some localCycle00354 else none) else (if id < 356 then (if id = 355 then some localCycle00355 else none) else (if id = 356 then some localCycle00356 else none))) else (if id < 358 then (if id = 357 then some localCycle00357 else none) else (if id < 359 then (if id = 358 then some localCycle00358 else none) else (if id = 359 then some localCycle00359 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 4, 3, 6, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 4, 1, 6], ![5, 0, 2, 3, 1, 6], ![4, 0, 2, 3, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 50 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1536)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 4, 6, 3, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 4, 6, 1], ![5, 0, 2, 3, 1, 6], ![4, 0, 2, 3, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 211 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1537)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 4, 6, 1], ![5, 0, 2, 3, 6, 1], ![4, 0, 2, 3, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 68 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1538)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 6, 4, 1], ![5, 0, 2, 6, 3, 1], ![4, 0, 2, 3, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 228 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1539)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 5, 6, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 2, 3, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 276 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1540)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 4, 6, 1], ![5, 0, 2, 3, 6, 1], ![4, 0, 2, 3, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 344 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1541)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 6, 4, 1], ![5, 0, 2, 6, 3, 1], ![4, 0, 2, 3, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 228 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1542)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 6, 5, 4, 1], ![5, 0, 2, 6, 3, 1], ![4, 0, 2, 6, 3, 1], ![0, 2, 4, 5, 3, 1]], proof := .tail 130 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1543)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 5, 6, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 2, 3, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 276 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1544)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 6, 5, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 2, 6, 3, 1], ![0, 4, 2, 5, 3, 1]], proof := .tail 130 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1545)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 5, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 6, 2, 3, 1], ![0, 4, 5, 2, 3, 1]], proof := .tail 209 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1546)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 5, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 6, 2, 3, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 217 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1547)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 4, 3, 2, 6], ![0, 5, 3, 4, 1, 6], ![0, 5, 2, 4, 1, 6], ![5, 0, 2, 3, 1, 6], ![4, 0, 3, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 55 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1548)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 4, 3, 6, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 4, 1, 6], ![5, 0, 2, 3, 1, 6], ![4, 0, 3, 2, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 55 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1549)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 4, 6, 1], ![5, 0, 2, 3, 1, 6], ![4, 0, 3, 2, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 169 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1550)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 4, 6, 1], ![5, 0, 2, 3, 6, 1], ![4, 0, 3, 2, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 106 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1551)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 6, 4, 1], ![5, 0, 2, 6, 3, 1], ![4, 0, 3, 2, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 222 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1552)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 3, 6, 4, 1], ![0, 5, 2, 6, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 3, 2, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 276 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1553)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 3, 4, 1], ![0, 5, 6, 2, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 202 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1554)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 4, 6, 1], ![5, 0, 2, 3, 6, 1], ![4, 0, 3, 2, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 39 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1555)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 6, 4, 1], ![5, 0, 2, 6, 3, 1], ![4, 0, 3, 2, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 222 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1556)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 3, 6, 4, 1], ![0, 5, 2, 6, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 3, 2, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 276 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1557)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 3, 4, 1], ![0, 5, 6, 2, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 3, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 202 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1558)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 3, 4, 1], ![0, 5, 6, 2, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 3, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 192 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1559)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 3, 4, 1], ![0, 6, 5, 2, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 0, 6, 3, 2, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 147 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1560)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 1, 6], ![0, 5, 4, 2, 1, 6], ![5, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 296 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1561)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 4, 3, 6, 2], ![0, 5, 4, 3, 6, 1], ![0, 5, 4, 2, 1, 6], ![5, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 76 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1562)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 3, 6, 1], ![0, 5, 4, 2, 6, 1], ![5, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 275 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1563)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 1], ![0, 5, 4, 6, 2, 1], ![5, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 218 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1564)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 3, 6, 1], ![0, 5, 4, 2, 6, 1], ![5, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 80 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1565)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![0, 5, 4, 6, 2, 1], ![5, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 348 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1566)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![0, 5, 4, 6, 2, 1], ![5, 0, 3, 6, 2, 1], ![4, 0, 3, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 319 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1567)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![0, 5, 6, 4, 2, 1], ![5, 0, 6, 3, 2, 1], ![4, 0, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 134 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1568)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 3, 6, 1], ![0, 5, 4, 2, 6, 1], ![5, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 132 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1569)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![0, 5, 4, 6, 2, 1], ![5, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 53 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1570)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![0, 5, 4, 6, 2, 1], ![5, 0, 3, 6, 2, 1], ![4, 0, 3, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 319 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1571)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![0, 5, 6, 4, 2, 1], ![5, 0, 6, 3, 2, 1], ![4, 0, 3, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 134 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1572)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![0, 5, 4, 6, 2, 1], ![5, 0, 3, 6, 2, 1], ![4, 0, 3, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 2 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1573)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![0, 5, 6, 4, 2, 1], ![5, 0, 6, 3, 2, 1], ![4, 0, 3, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 334 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1574)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![0, 6, 5, 4, 2, 1], ![5, 0, 6, 3, 2, 1], ![4, 0, 6, 3, 2, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 126 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1575)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 5, 6, 4], ![0, 1, 3, 5, 6, 4], ![0, 1, 2, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 2, 3, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 9 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1576)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 5, 6, 4], ![0, 1, 3, 5, 6, 4], ![0, 1, 2, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 2, 6, 3], ![4, 0, 1, 2, 5, 3]], proof := .tail 323 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1577)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 5, 6, 4], ![0, 1, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 6, 2, 3], ![4, 0, 1, 5, 2, 3]], proof := .low6 (![225, 64, 27, 173, 32, 16, 186, 307, 277, 54, 119, 311, 15, 339, 157, 18, 201, 15, 103, 306, 24, 15, 234, 62, 247, 95, 184, 82]) }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1578)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 5, 6, 4], ![0, 1, 6, 3, 5, 4], ![0, 1, 6, 2, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 6, 2, 3], ![4, 0, 1, 5, 3, 2]], proof := .tail 349 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1579)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 5, 6, 4], ![0, 1, 5, 3, 6, 4], ![0, 1, 5, 2, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 3, 2, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 254 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1580)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 5, 6, 4], ![0, 1, 5, 6, 3, 4], ![0, 1, 5, 6, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 3, 2, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 20 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1581)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 5, 6, 4], ![0, 1, 6, 5, 3, 4], ![0, 1, 5, 6, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 3, 6, 2], ![4, 0, 1, 3, 5, 2]], proof := .tail 138 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1582)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 5, 6, 4], ![0, 1, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 6, 3, 2], ![4, 0, 1, 5, 3, 2]], proof := .tail 86 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1583)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 6, 5, 4], ![0, 1, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![4, 0, 5, 1, 2, 3]], proof := .low6 (![183, 64, 128, 274, 256, 16, 186, 271, 124, 52, 205, 129, 15, 221, 67, 123, 201, 15, 312, 255, 48, 15, 93, 13, 332, 46, 229, 82]) }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1584)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 3, 5, 4], ![0, 1, 6, 2, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![4, 0, 5, 1, 3, 2]], proof := .tail 349 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1585)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 3, 2], ![4, 0, 5, 1, 3, 2]], proof := .tail 86 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1586)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![4, 0, 5, 3, 1, 2]], proof := .tail 121 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1587)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 3, 2], ![4, 0, 5, 3, 1, 2]], proof := .tail 167 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1588)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 5, 3, 6, 4], ![0, 1, 5, 3, 6, 4], ![0, 5, 1, 2, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 1, 2, 6], ![4, 0, 1, 2, 3, 5]], proof := .low6 (![90, 64, 345, 116, 92, 210, 42, 94, 329, 214, 143, 313, 206, 320, 137, 79, 313, 206, 290, 78, 313, 206, 113, 313, 151, 230, 249, 313]) }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1589)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 5, 3, 6, 4], ![0, 1, 5, 6, 3, 4], ![0, 5, 1, 6, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 1, 2, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 278 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1590)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 5, 3, 6, 4], ![0, 1, 6, 5, 3, 4], ![0, 5, 1, 6, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 1, 6, 2], ![4, 0, 1, 3, 5, 2]], proof := .tail 187 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1591)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 5, 6, 3, 4], ![0, 1, 5, 6, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 1, 2, 6], ![4, 0, 3, 1, 2, 5]], proof := .low6 (![181, 125, 263, 238, 233, 260, 42, 96, 246, 99, 179, 84, 236, 175, 287, 127, 220, 49, 340, 194, 156, 107, 282, 63, 89, 115, 158, 40]) }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1592)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 5, 6, 3, 4], ![0, 1, 6, 5, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 1, 6, 2], ![4, 0, 3, 1, 5, 2]], proof := .tail 226 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1593)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 6, 1, 2], ![4, 0, 3, 5, 1, 2]], proof := .tail 248 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1594)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 3, 1, 2], ![4, 0, 5, 3, 1, 2]], proof := .tail 195 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1595)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![4, 0, 5, 3, 2, 1]], proof := .tail 308 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1596)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 3, 2], ![4, 0, 5, 3, 2, 1]], proof := .tail 167 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1597)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 6, 1, 2], ![4, 0, 3, 5, 2, 1]], proof := .tail 265 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1598)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 3, 1, 2], ![4, 0, 5, 3, 2, 1]], proof := .tail 195 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1599)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 2, 3, 6, 4], ![0, 5, 1, 3, 6, 4], ![0, 5, 1, 2, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 2, 1, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 59 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1600)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 2, 3, 6, 4], ![0, 5, 1, 6, 3, 4], ![0, 5, 1, 6, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 2, 1, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 237 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1601)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 2, 6, 3, 4], ![0, 5, 1, 6, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 2, 1, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 245 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1602)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 2, 3, 4], ![0, 5, 6, 1, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 5]], proof := .tail 136 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1603)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 2, 3, 4], ![0, 5, 6, 1, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 5, 1]], proof := .tail 268 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1604)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 6, 2, 1], ![4, 0, 3, 5, 2, 1]], proof := .tail 45 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1605)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 3, 4], ![0, 6, 5, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 3, 2, 1], ![4, 0, 5, 3, 2, 1]], proof := .tail 29 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1606)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 2, 5, 6, 4], ![0, 3, 1, 5, 6, 4], ![0, 2, 1, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 2, 3, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 170 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1607)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 2, 5, 6, 4], ![0, 3, 1, 5, 6, 4], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 2, 6, 3], ![4, 0, 1, 2, 5, 3]], proof := .tail 309 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1608)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 2, 5, 6, 4], ![0, 3, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 6, 2, 3], ![4, 0, 1, 5, 2, 3]], proof := .tail 109 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1609)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 2, 6, 5, 4], ![0, 3, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![4, 0, 5, 1, 2, 3]], proof := .low6 (![183, 64, 128, 274, 350, 6, 100, 271, 124, 52, 205, 98, 5, 221, 67, 44, 98, 302, 312, 255, 98, 356, 93, 98, 332, 73, 58, 98]) }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1610)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 6, 2, 5, 4], ![0, 3, 6, 1, 5, 4], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![4, 0, 5, 2, 1, 3]], proof := .tail 176 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1611)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 3, 2, 5, 4], ![0, 3, 6, 1, 5, 4], ![0, 2, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![4, 0, 5, 2, 3, 1]], proof := .tail 343 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1612)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 3, 2, 5, 4], ![0, 6, 3, 1, 5, 4], ![0, 6, 2, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![4, 0, 5, 3, 2, 1]], proof := .tail 65 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1613)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 5, 2, 6, 4], ![0, 3, 5, 1, 6, 4], ![0, 2, 1, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 1, 3, 6], ![4, 0, 1, 2, 3, 5]], proof := .low6 (![90, 64, 345, 267, 317, 240, 7, 94, 329, 214, 35, 150, 250, 320, 204, 79, 171, 250, 290, 78, 171, 250, 101, 51, 31, 8, 338, 298]) }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1614)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 5, 2, 6, 4], ![0, 3, 5, 1, 6, 4], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 1, 6, 3], ![4, 0, 1, 2, 5, 3]], proof := .tail 289 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1615)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 3, 2, 6, 4], ![0, 3, 5, 1, 6, 4], ![0, 2, 5, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 3, 1, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 77 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1616)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 3, 2, 6, 4], ![0, 5, 3, 1, 6, 4], ![0, 5, 2, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 2, 1, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 223 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1617)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 5, 6, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 1, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 1, 3, 6], ![4, 0, 2, 1, 3, 5]], proof := .low6 (![215, 325, 188, 139, 216, 240, 7, 324, 291, 36, 131, 190, 314, 191, 36, 26, 219, 14, 337, 353, 353, 353, 301, 318, 36, 112, 272, 85]) }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1618)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 5, 6, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 1, 6, 3], ![4, 0, 2, 1, 5, 3]], proof := .low6 (![215, 325, 188, 139, 316, 279, 105, 324, 291, 36, 262, 305, 164, 191, 36, 28, 305, 14, 337, 208, 305, 353, 283, 305, 36, 180, 61, 305]) }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1619)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 6, 5, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 6, 1, 3], ![4, 0, 2, 5, 1, 3]], proof := .tail 253 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1620)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 6, 5, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 2, 1, 3], ![4, 0, 5, 2, 1, 3]], proof := .tail 153 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1621)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 3, 5, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 6, 1, 3], ![4, 0, 2, 5, 3, 1]], proof := .tail 71 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1622)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 3, 5, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 2, 1, 3], ![4, 0, 5, 2, 3, 1]], proof := .tail 153 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1623)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 3, 5, 2, 4], ![0, 6, 3, 5, 1, 4], ![0, 6, 2, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 2, 1, 3], ![4, 0, 5, 3, 2, 1]], proof := .tail 315 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1624)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 3, 6, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 5, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 3, 1, 6], ![4, 0, 2, 1, 3, 5]], proof := .tail 148 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1625)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 3, 6, 2, 4], ![0, 5, 3, 6, 1, 4], ![0, 5, 2, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 2, 1, 6], ![4, 0, 2, 1, 3, 5]], proof := .tail 12 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1626)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 3, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 5, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 3, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 38 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1627)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 3, 2, 4], ![0, 5, 3, 6, 1, 4], ![0, 5, 2, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 2, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 56 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1628)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 3, 2, 4], ![0, 5, 6, 3, 1, 4], ![0, 5, 6, 2, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 5]], proof := .tail 286 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1629)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 5, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 3, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 288 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1630)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 6, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 6, 3, 1], ![4, 0, 2, 5, 3, 1]], proof := .tail 195 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1631)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 6, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 2, 3, 1], ![4, 0, 5, 2, 3, 1]], proof := .tail 104 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1632)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 2, 4], ![0, 6, 3, 5, 1, 4], ![0, 6, 2, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 2, 3, 1], ![4, 0, 5, 3, 2, 1]], proof := .tail 23 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1633)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 2, 4], ![0, 5, 3, 6, 1, 4], ![0, 5, 2, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 2, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 33 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1634)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 2, 4], ![0, 5, 6, 3, 1, 4], ![0, 5, 6, 2, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 5, 1]], proof := .tail 185 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1635)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 1, 4], ![0, 5, 6, 2, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 6, 2, 1], ![4, 0, 3, 5, 2, 1]], proof := .tail 153 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1636)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 1, 4], ![0, 6, 5, 2, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 3, 2, 1], ![4, 0, 5, 3, 2, 1]], proof := .tail 159 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1637)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 5, 6, 4], ![0, 1, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 1, 3, 2, 6], ![4, 0, 1, 3, 2, 5]], proof := .low6 (![258, 224, 244, 178, 168, 260, 42, 155, 160, 199, 154, 304, 57, 193, 120, 144, 251, 206, 341, 232, 200, 206, 261, 17, 114, 252, 21, 40]) }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1638)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 5, 3, 6, 4], ![0, 1, 5, 6, 4, 3], ![0, 5, 1, 6, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 1, 2, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 22 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1639)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 5, 6, 3, 4], ![0, 1, 5, 6, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 1, 2, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 174 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1640)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 5, 6, 4], ![0, 1, 6, 5, 4, 3], ![0, 1, 5, 6, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 1, 3, 6, 2], ![4, 0, 1, 3, 5, 2]], proof := .tail 41 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1641)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 5, 6, 4], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 1, 6, 3, 2], ![4, 0, 1, 5, 3, 2]], proof := .tail 30 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1642)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 6, 1, 3, 2], ![4, 0, 5, 1, 3, 2]], proof := .tail 30 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1643)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 6, 1, 3, 2], ![4, 0, 5, 3, 1, 2]], proof := .tail 330 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1644)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 5, 3, 6, 4], ![0, 1, 6, 5, 4, 3], ![0, 5, 1, 6, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 1, 6, 2], ![4, 0, 1, 3, 5, 2]], proof := .tail 351 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1645)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 5, 6, 3, 4], ![0, 1, 6, 5, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 1, 6, 2], ![4, 0, 3, 1, 5, 2]], proof := .tail 174 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1646)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 6, 1, 2], ![4, 0, 3, 5, 1, 2]], proof := .tail 72 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1647)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 6, 3, 1, 2], ![4, 0, 5, 3, 1, 2]], proof := .tail 162 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1648)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 6, 1, 3, 2], ![4, 0, 5, 3, 2, 1]], proof := .tail 330 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1649)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 6, 1, 2], ![4, 0, 3, 5, 2, 1]], proof := .tail 72 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1650)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 6, 3, 1, 2], ![4, 0, 5, 3, 2, 1]], proof := .tail 162 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1651)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 2, 3, 6, 4], ![0, 5, 1, 6, 4, 3], ![0, 5, 1, 6, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 2, 1, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 70 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1652)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 2, 6, 3, 4], ![0, 5, 1, 6, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 2, 1, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 174 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1653)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 2, 3, 4], ![0, 5, 6, 1, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 5]], proof := .tail 285 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1654)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 2, 3, 4], ![0, 5, 6, 1, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 5, 1]], proof := .tail 72 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1655)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 6, 2, 1], ![4, 0, 3, 5, 2, 1]], proof := .tail 359 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1656)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 4, 3], ![0, 6, 5, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 6, 3, 2, 1], ![4, 0, 5, 3, 2, 1]], proof := .tail 162 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1657)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 3, 1, 2, 6], ![4, 0, 3, 1, 2, 5]], proof := .low6 (![66, 239, 3, 335, 118, 260, 42, 155, 83, 342, 122, 326, 347, 110, 322, 10, 251, 206, 60, 198, 4, 206, 75, 63, 321, 115, 1, 40]) }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1658)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 3, 1, 6, 2], ![4, 0, 3, 1, 5, 2]], proof := .low6 (![163, 273, 43, 331, 316, 142, 284, 257, 87, 231, 303, 295, 11, 69, 322, 266, 295, 299, 152, 0, 295, 81, 300, 295, 172, 177, 293, 295]) }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1659)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 3, 6, 1, 2], ![4, 0, 3, 5, 1, 2]], proof := .low6 (![163, 235, 213, 166, 197, 196, 270, 242, 281, 357, 354, 328, 11, 243, 297, 327, 336, 145, 34, 91, 25, 165, 310, 161, 297, 140, 141, 108]) }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1660)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 3, 6, 1, 2], ![4, 0, 3, 5, 2, 1]], proof := .tail 294 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1661)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 3, 2, 1, 6], ![4, 0, 3, 1, 2, 5]], proof := .low6 (![66, 239, 3, 335, 350, 133, 135, 155, 83, 342, 122, 182, 74, 110, 322, 97, 182, 203, 60, 198, 182, 358, 75, 182, 321, 333, 111, 182]) }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1662)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 5]], proof := .low6 (![212, 241, 352, 146, 259, 207, 227, 264, 88, 280, 117, 19, 149, 88, 280, 117, 19, 37, 269, 346, 88, 88, 102, 292, 292, 47, 189, 355]) }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1663)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (1536 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 1536 ≤ id.val) (hhigh : id.val < 1664) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 1536)) = true := by
  let j : Fin 128 := ⟨id.val - 1536, by omega⟩
  have hsum : 1536 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (1536 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard012
