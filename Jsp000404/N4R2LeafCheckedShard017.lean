import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard017
open N4R2RowDataReplay

-- Original cycle 045177addd8632b6124533fe8877185d39e178582f6b5af61a0fece59458aad1; original global index 341.
def localCycle00000 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 2, .triangle 14 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 04c930e477bbf32291c5fead18c0529fc02ba8a488757fb325042c1176c8e307; original global index 385.
def localCycle00001 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -3, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .gapLower 6 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 05dbcbf0543f500c48e20b9c27d9a6a5cdc5adb4e31f9ce3bce97674fda93b1f; original global index 486.
def localCycle00002 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 0720ebaa2e5c908014a8a7432b84a933e6f8c24ef0c855112d54e61078b2427c; original global index 588.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -2, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .gapLower 6 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 0b34220e671689e8b4ad4d524ee4f62c27a5b29bc6abc704892fd51fdcbd99b3; original global index 895.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 0ccdab088c5038e8d2a050b5a208a5b1fef9a7d1fef43940d22c7f387679cfbf; original global index 1014.
def localCycle00005 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 2 4]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 29 1]

-- Original cycle 116985dcd8e2f7b9b23f3ffcbf3a423769a819d9305817bf59c18e7360a4829f; original global index 1388.
def localCycle00006 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 2, .triangle 24 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 13582a71dbe9951e3c14ccbf86657c784a8994863224d0e81c46b21e717fd9e1; original global index 1524.
def localCycle00007 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 13ca43ce2f19cdbe00caea30a978ac43133feaaf8bc6a9035d1d45391b1afb64; original global index 1571.
def localCycle00008 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 13e93fc6bd9a20d57f5c127e266d8d3ae2ff78855ffe8afd3312163c46221455; original global index 1574.
def localCycle00009 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 2, .triangle 20 1, .triangle 33 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 14e53783d5d6ac7afd8a2075ccfad25336375bd41e84208de3aea65e32622f3b; original global index 1658.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 33 1, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 156b777143e47af89725913aaccc1759e20ee561de4259c78bbed3f3d93f30cb; original global index 1696.
def localCycle00011 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 2, .gapUpper 5 2]

-- Original cycle 17136d88e3ee2678ad9cf59029a7260208790130715056cb2d3ca8c0951288fd; original global index 1815.
def localCycle00012 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 1805a62aea68589f67b7133c8d391ab68ab5f8f38f7374c61030f9616416ba1c; original global index 1878.
def localCycle00013 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -2, 0, -2, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 24 2, .gapLower 6 1, .triangle 14 1, .triangle 10 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 1b6a60390756636a152ec455e6eb605d567c60813996d53c9d282e6178197021; original global index 2125.
def localCycle00014 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 15 1, .triangle 17 0, .triangle 28 1, .triangle 31 2, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 1ddf19a39a831bc3bfa6551ce4c9d9660b796a44e69d300496835e11cf9d66ec; original global index 2294.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 30 1, .gapLower 6 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 20511e8ac3f85a3ee9effa9bc538e39a0b198970598ee2197f7d320a72571cf5; original global index 2476.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 22b7176449a6cff42e4f52e6910bd01a8f9555eb3ac88252c38fd3f83ed3c448; original global index 2661.
def localCycle00017 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 0, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 22c44e5c7feda75088c9afabfe82c394755da26df4523b38dad7f52f25fdb3cc; original global index 2662.
def localCycle00018 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 23b8e7da62cfd425bed72e408ac623fe45434c2d78517bba2ff1c943bc4ea6f2; original global index 2740.
def localCycle00019 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 2562ab2a7daf9db6417384416663f0e7349f5b9606c3ed61d5219d2bc9b7a81f; original global index 2876.
def localCycle00020 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 260fbb16e17c63d7dc57ca781f2eca6d911f91ef47e8eee8d749018faa09eb6c; original global index 2917.
def localCycle00021 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 3 2, .triangle 10 1, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 2958fb68c875ad3854699bdb4e1a014a9915ca8a8d6a576cf8d831eedce3f2b6; original global index 3155.
def localCycle00022 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 2af08d5770eaf2d8ec0458d5aa668a1ea83cbfb96accad29ae8abd72be967a7d; original global index 3274.
def localCycle00023 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 2b0da0828d2c2521c22af4b350e8322f67dcae8c2596b5983df6e8268d60864f; original global index 3286.
def localCycle00024 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 34 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 2c6fd557fb99f1500c9d150ce2833bc21c27e7265870955496905f4539b5ec46; original global index 3395.
def localCycle00025 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 27 0, .triangle 21 0, .triangle 15 1, .triangle 16 0, .triangle 6 2, .triangle 9 1, .corridorLower 3 4]

-- Original cycle 32b0e15164015457e2751a583cb25e41ab470254498e738cedafb28ecd6e4f65; original global index 3880.
def localCycle00026 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 340283654a1e58fbd16595e447d0183eca017914b753ab042e6474cd079afe96; original global index 3986.
def localCycle00027 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 361d1484713526ec84705044afb0efc9fc1dcee6aa2438de55e51511700e24aa; original global index 4154.
def localCycle00028 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle 367f87debd3d9fe79dbfb203692c8463af6f8f160c57c190c98377406012e204; original global index 4183.
def localCycle00029 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .gapLower 3 3, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 3702df67174d5eb887eb9533283ebf2e86aa162f182e9a6c4016e3526e682199; original global index 4222.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 389491ec4695415f7a1b93d460cb3076354d29a66da124b21d2a468fefdf08a4; original global index 4353.
def localCycle00031 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 3b06ad2d86b9d10a5cf79e675dc3fc0a863f3a47067e510c14dd03cece0760c8; original global index 4559.
def localCycle00032 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 2 6, .distance 2 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .triangle 27 1]

-- Original cycle 3ee0f9c5b257a1ac887a145e418377cb87bb9c5718c90bcc02e8656c29f2e563; original global index 4860.
def localCycle00033 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 2, .triangle 33 1, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 41a0c60a87eb593cf55019fbd84d160747874967eb0090451e82c6f2fcbbc23d; original global index 5060.
def localCycle00034 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 26 1, .triangle 15 0, .triangle 16 0, .triangle 6 2, .triangle 9 1, .corridorLower 3 4]

-- Original cycle 4266614f088427d2b310ee8dd047b93443adb68d18d6e0a7e145e2accabdea64; original global index 5115.
def localCycle00035 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 24 1, .gapLower 6 1, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 42e31e6f75db7b18ed5cf5f4751ca36a32b93f48622acd972c7c64f7ee5092e8; original global index 5149.
def localCycle00036 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 43111f4ba975dffc96d4e772aa89556a0eed3c13cbd47ed91939dc9f70720066; original global index 5176.
def localCycle00037 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .triangle 1 2, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 4724eb4e3e52e0c0cc43ba37bb715ef8551425795c4637fec6b8d1f3abc76568; original global index 5518.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .gapLower 1 4, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 4974f9986217de0466465703ac3b95532588be56a723f3e9266bc4e6cf2ea5cc; original global index 5692.
def localCycle00039 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle 49e6cd037f08cd94e97b16714329c8961268e99cfc96542d8258d67bcc75768f; original global index 5733.
def localCycle00040 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -3, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 2, .gapLower 6 1, .triangle 14 1, .triangle 10 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 4ce0b024b0129dac5d6573b5063a015b123db85f131ca6b337e962caf928f3b1; original global index 5970.
def localCycle00041 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 0, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 4cf718541e26c6468d8ed3c6de886332e70b760826006d38e738ed4d45c96b3d; original global index 5978.
def localCycle00042 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 4d86bda4b79ec46f2270b5e15255f3ceb6eade89bc1747c3891a0f3e9754dc10; original global index 6020.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 27 2, .gapLower 6 3, .triangle 24 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 4f49981b09732e9d2cf9cbbdeb216c4f82488d57ffafd43168eac46d44931116; original global index 6161.
def localCycle00044 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 2, .gapUpper 3 5]

-- Original cycle 530be4b298c37e2681e402e319ae45aed25d83660f169884e258a0b738a29e1b; original global index 6465.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 1, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 538ead5c8fc5bccee657d34b6cc407709d4c7dd610a220630b89de2433d2fe95; original global index 6494.
def localCycle00046 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 5903a6ca128255576202bd2e00232a7114219ecc9282fc2ed7410667958ea1d7; original global index 6901.
def localCycle00047 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 1 2, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 5cc79a7fef8f8c69084f8a7435ef46e1bea3a62c2715950098a64213ca02f6ca; original global index 7221.
def localCycle00048 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 33 1, .triangle 20 0, .triangle 1 2, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 5e9d348df1212f9d94801397a756b9e8e43fc62f0e6243bc876b988d9856a847; original global index 7357.
def localCycle00049 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 5ebe9362b2d027bc3339b5220610768e0bd83de7891492731cd228107295685e; original global index 7375.
def localCycle00050 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 5f48a84757730225bb28b08b1225e809a42305d2284e41facb35e1c461b34ddc; original global index 7418.
def localCycle00051 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .gapLower 1 4, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 61c013adcbbdcaa017c9de286a13ddb959bb98ee90330ed2758acfa446eed26e; original global index 7629.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 703a3eeb1f8d8bef8336a05f5094fb594d88eb7b93a3e094f03de8b8f3b60e0a; original global index 8692.
def localCycle00053 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 7335c7c305fe4a98912d4d1260139ef24c1bff6154be09a85bfb1353615a59d8; original global index 8921.
def localCycle00054 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 74d2e5d145c7a83f24fc9639aaa6f08261a14a579b8989647babec2b6d65d755; original global index 9050.
def localCycle00055 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 79de41ef57e91cb87da3f4c6db64082d1b2f159e0e2c90d766d82a675685fb6d; original global index 9425.
def localCycle00056 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 26 1, .triangle 20 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 7b36157054b4593a45a1b5c3e1a9778184fea184fdd6bcd83d3202b7d8d5af5a; original global index 9542.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 7d844ac8d6f508b364c56c5e79001e6388ebe6c7a65380fb8da51a1922a898cf; original global index 9742.
def localCycle00058 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 80773b57a2cb622302cdf34baa2e39ff0965b59dcd9a55fb1bbf5bddc7073c54; original global index 9969.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 0, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 31 2, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 80aab3c051bd825c936e2974aed83e7423e888535e2b9176628a953179999362; original global index 9989.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 24 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 815029151330f4b3ccf646b35ca1b8333dc99f6a75093789ccfb46ad8747ccda; original global index 10040.
def localCycle00061 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 8369fb6752243115fdfee71b0cf84f688866256cd314f757833f749cf88782a9; original global index 10193.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .gapLower 6 2, .triangle 4 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 83986cae57bdea91fdac6464e214d58b8896ee1bbd986d9ff1f66304b33eccfd; original global index 10216.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 0, .triangle 14 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 849b8b825440c4c2d1797a70dd9b817a02a3c74526d750cd19b8fed54418fd2d; original global index 10298.
def localCycle00064 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 87b7e195241c0c86f1c6bde4693cdceaa6423f44045d3b0641ff3a04c300f95e; original global index 10520.
def localCycle00065 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 8b32da8c252bbfb1f1b793bd0467b9c1a07330811074ecc6383be3a16cefe53f; original global index 10783.
def localCycle00066 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, false, false, false, true, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 8e17251990210b35d356a85958c6d92052bc484744ae532432be50ce64ce5159; original global index 11004.
def localCycle00067 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2]
    constant := ![0, 2, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 16 2, .gapUpper 4 4, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .gapLower 1 3]

-- Original cycle 8f3dd8ccc270b105c829e8b87eb6f3b3852d7d94c5e838734f3ea4b55fc0f93e; original global index 11084.
def localCycle00068 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 16 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 900f1ac86a30fa71badf225111d94327dc421fd1bd4aacf0097e236d97833f53; original global index 11151.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 3 5, .distance 1 3, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 20 0, .triangle 1 2, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 930f9d3fdbc1be9d7562de2453ceaa1b5781ad28364a83182e14a752779190a9; original global index 11402.
def localCycle00070 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 33 1, .triangle 20 0, .triangle 15 1, .triangle 16 0, .triangle 6 2, .triangle 9 1, .corridorLower 3 4]

-- Original cycle 9404e8bd38cc2243ee874efe9525936c2a626b453065978939aa9bc465eecd68; original global index 11480.
def localCycle00071 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 9bfc1151afc7483cca78bedfb558c99eb5f13dfd5e6e34d686be6dc810dc5edc; original global index 12132.
def localCycle00072 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 22 0, .triangle 16 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 9c60a6737b331be44ed24b723f0cf2e438a6f452e8e10f208dd780f38ba15ba5; original global index 12165.
def localCycle00073 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle 9db375dc95e9b95a728af240510878661517b149b8d70590a33e34c4e671d0fb; original global index 12270.
def localCycle00074 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 28 0, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 9dccc4f771008661f5b9d5f75a159e4ddfeee4c770ce31ba2ff99072db412e06; original global index 12277.
def localCycle00075 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 2 3]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 2 3, .gapUpper 4 4, .gapLower 6 5, .triangle 27 0]

-- Original cycle 9ef9344b8acf87092a6f5c523db549e8dbb98e33fb477b8e59dd968b002febe8; original global index 12379.
def localCycle00076 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle a1fe57f771416b7ffa9ae228487b313f78ae31303601ccc029a4ead805606111; original global index 12597.
def localCycle00077 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 1, .gapLower 6 1, .triangle 14 1]

-- Original cycle a26ec7336222745d0d458c501c14f4f8251c84e1d0efdf6b7fb176364539fb96; original global index 12635.
def localCycle00078 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle a2ca44772acb141e3a9aafde670d8dce15ee9753c3e8d8e2842272309cf9f895; original global index 12659.
def localCycle00079 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle a2cb7e8d1e3c3e4ca55aaf88b71f681d5f0d44bff828cdf2c755d3238e17a9f5; original global index 12660.
def localCycle00080 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .gapLower 1 4, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle a2f8de091ff89824eeba94cf49e3c1b5fc75c69c872bb7243dabb652cbf5dee1; original global index 12674.
def localCycle00081 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .triangle 3 2, .triangle 10 1, .triangle 9 0, .corridorLower 3 4]

-- Original cycle a4fca8e0362458fb5b9db3c2c7aa5bc622875ee7c15bb48a883fea06177431cb; original global index 12823.
def localCycle00082 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .triangle 15 1, .triangle 16 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle a6341429e1e79af67064f3fa9f2b6c5acd1cf2a3a00c1077bc364db533a58ae0; original global index 12911.
def localCycle00083 : Cycle where
  length := 13
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, 2, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 2, .gapUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle a6fe51bac39ce5ed7e755131ba05e23ffd34879337f989889a2e66ff5e04fee7; original global index 12979.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle a7cde0dcb84ff69115e42481cced0bc2e4accb9a34b26909ef32f01b3ff63dcf; original global index 13057.
def localCycle00085 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle a87886e2cab62a77f885bb3a39fb819c94e5b1081703cf4e2f9c981683d385ae; original global index 13111.
def localCycle00086 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 31 2, .triangle 33 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4]

-- Original cycle a934f7c8bf18d13b30b4ef4a7b7a1d304e32e5b5d61bd027059cc1263623002e; original global index 13176.
def localCycle00087 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 33 1, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle af820c6d7a08aba8504d3cce1a400e1c5b36e7e4e58d9ab916f73d4556db4d48; original global index 13706.
def localCycle00088 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -3, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 24 1, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle b03c1b4d343087020b86382034c6831388843f98d7f13394842011e1ab969810; original global index 13758.
def localCycle00089 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle b0c795e7f5ebab0d098dee0547261c1fcb5649690305a952d5d995040cdc5f1b; original global index 13805.
def localCycle00090 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle b1c9159773e4a8e75830f5be9c9cc063d1d72b4c0843367b89c06630855d8fc8; original global index 13895.
def localCycle00091 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 9 0, .triangle 11 0, .triangle 33 1, .corridorLower 3 5]

-- Original cycle b255888ce60eba02a72ee82c6a0fca5decebafeeb4087f8a949cb438c13a5acd; original global index 13938.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 33 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4]

-- Original cycle b3baccb36fa46266b06ff4ed6340a21ee7b6a0ea8cd3dd8feadd8d125b21e936; original global index 14038.
def localCycle00093 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 33 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4]

-- Original cycle b45a5ff4f66b008de04260a67ba377aadd55d7041872278f5795c262d82f4e18; original global index 14090.
def localCycle00094 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Original cycle ba43c6f041d4178ddec68b767e9462af85d07849f005f2bccfb0660dc5604ad8; original global index 14543.
def localCycle00095 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, false, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 2, .gapLower 6 1, .triangle 14 1, .triangle 10 1, .triangle 9 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle c079249653540772f03b23042654b4562ccd3c20e8689a7effe23f6a5f11fad5; original global index 15023.
def localCycle00096 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 6, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 0, .gapLower 6 1, .triangle 11 1, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle c149e9c9987dd872cd8bb26d7d775567f41c6f566f16ccef2b549e5544e4bfed; original global index 15092.
def localCycle00097 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle c179d9330fa0047572cc1701f6d239a270d88550d875de0873dbec388b0581fd; original global index 15109.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle c3565392f2aa49272e6a16d29be442d21a76163858e87649710ea66d4a9754be; original global index 15240.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle c39c0b5e80e83d7507b8208651d2d68fe44426c93c1a52d0d9d92aed544c94e6; original global index 15267.
def localCycle00100 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 24 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle c414ee051bf3544824883665b1a774e94e09e0fb36c90694b6d910dcc85cec0e; original global index 15295.
def localCycle00101 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle c4b2e937a2768b3ed2c0b4f8ea73a6d4e66cfe4f70e8f36e9423eb60994a1c1a; original global index 15341.
def localCycle00102 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle c5101da9b20e0f261afbfeb22af1eca859b3b1ad88075e956ced4ac29a9822c3; original global index 15376.
def localCycle00103 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 2 3]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 2 3, .gapUpper 4 4, .gapLower 6 5, .triangle 27 0]

-- Original cycle c54dd25c2f521e914ecf3e8ca9453e8797bea1c8a81cecdee1fcfe4f63442f1d; original global index 15392.
def localCycle00104 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle c567b859efa0ec379bf247c298ecb694cbda6461870a795bd1b34e3bc51915bf; original global index 15399.
def localCycle00105 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle c6c7778bd569582c69d875ae3b4d78989c350bc68f5fadf5e7ca64319589ddf9; original global index 15512.
def localCycle00106 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle c757fbf6e823ab413aad8498ee763c0f677d9a6114447a1a544473ef44547a44; original global index 15556.
def localCycle00107 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle c7b8e6f06d5f925c04325874f823a4e04b188196715fb217fb990099a1a17c30; original global index 15590.
def localCycle00108 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .triangle 20 1, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle c853a517e770230a71e18bd715c5bc51484080e51369615e819317c0e269396a; original global index 15637.
def localCycle00109 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle c91f4918773f19056cece125598b4702670b464374c52b9a85aceedb78b22689; original global index 15712.
def localCycle00110 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 18 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle ca5e60c41d577c5960523c3aeb0839650a1e4753c48b8ed5381775b97af97f09; original global index 15818.
def localCycle00111 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .triangle 24 1, .gapLower 6 1, .corridorLower 0 6, .thetaLower 0]

-- Original cycle cb02088b1cdd07332c3a8df11713ccfd604cc5091777cdc966860f6f8071299c; original global index 15862.
def localCycle00112 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -3, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 24 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle cbb5d620eb6af0b6a03663f016deb83c4b5b0b9e2c7650e0f116147fccb13c7e; original global index 15915.
def localCycle00113 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 9 0, .triangle 11 0, .triangle 33 1, .corridorLower 3 5, .thetaNext 2]

-- Original cycle cd691b367a373569177be3c7c8eb7014226edd0a19cec76bc6959bef48846484; original global index 16056.
def localCycle00114 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle cde9965d133a8a3c7c34903c03dc6c76e21eed1bdb0e93a966687cead21481ba; original global index 16081.
def localCycle00115 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .gapLower 6 3, .triangle 24 1, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle d04414905b848fc5ad8d7d6fdb54352ed0190fe86587b53498457bf8c1024e51; original global index 16255.
def localCycle00116 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle d2e143c673f55c6e1eea346fb41b0415a2f38411ff46376592c2ccf03c22cb46; original global index 16452.
def localCycle00117 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 26 1, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle d37bf5f93784e8dc18d10f7210db850f0c03e26f41f34076669d1e34082e9972; original global index 16501.
def localCycle00118 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle d4d3fb3ca57fee1251977f836944f996f00dd484d528ac82297fb92083addcb8; original global index 16603.
def localCycle00119 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 24 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle d65642200682fb5f815bef901bdc445b21b5d94a8c46a5cc2e15d1a5cddc2e3c; original global index 16734.
def localCycle00120 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 18 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle d7b83786348647ad6c93771a8040b7fa626eb01c861b453d684e6dba0ff4f235; original global index 16834.
def localCycle00121 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 31 2, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle d8a78dfaf75d2733a1a281d3eb2d5fb6a6db776d893bb019e8ed7278ed22859b; original global index 16912.
def localCycle00122 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle dc53bdccb15684a1f20733223e7b2513900fc98cafb03a91c59bbffea56b35e0; original global index 17218.
def localCycle00123 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle dec14fdb4f359365f324802f076b3fac697c4d7bb0d1d7d582dadc9346e8138d; original global index 17416.
def localCycle00124 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle e071808357eccf606f35ce8c31e175f7372c1fb1747cfb4b99fb0c1f6cfed2e4; original global index 17548.
def localCycle00125 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 4, .gapLower 1 3, .triangle 16 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle e0f0cb317d0adb7c0e51dc0f535dfac1f98063f6b0e188b271c2488fcaff1745; original global index 17590.
def localCycle00126 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle e1f727a72010f05bf9de0027966243850c1e02463307964f2becf5e10ab69e77; original global index 17669.
def localCycle00127 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 26 1, .triangle 20 0, .triangle 15 1, .triangle 16 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle e43e77764ca2c0a548965893d6aba4ef70d61844288d872b19b1a490d527f78b; original global index 17846.
def localCycle00128 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle e73c95acc55dd90ac2816e4ceab8b8830ef9c88ab95bd656e015364bf9a92eaa; original global index 18087.
def localCycle00129 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle e7d80fe7efdc9f38daf7b685c0ace0dbd4b2c129fed9ac882ae4469d6cf020ae; original global index 18130.
def localCycle00130 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapLower 6 2, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle e8671c95d6c07f4de0d767ddea4b04c2fff6b4135390dcf4d787f822c1aef059; original global index 18168.
def localCycle00131 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .gapLower 6 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle ed8105de128ae87166cbcd1326fb417d2b2633f97c2404c2c11621955dbf8007; original global index 18542.
def localCycle00132 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 2, .triangle 24 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4]

-- Original cycle f21423c39751033c992705f989a3d7e008ad9f9e29810a3f1d6015ca138e5d26; original global index 18878.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .gapLower 1 3, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle f22ff5c91a12776b13c2ca1eb68279474268a0c6d5ef397f9a370203ab22860e; original global index 18889.
def localCycle00134 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle f2a099cd6e5851f6534bf27cc1d939b791ed1fb35c7db80c4f255ec815db72f0; original global index 18913.
def localCycle00135 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4]

-- Original cycle f32d8528c50ea6f84b474e6c50021b15fe32a4e13594e6dfd98f46d74e180be3; original global index 18958.
def localCycle00136 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 23 0, .gapLower 1 3, .triangle 17 0, .triangle 28 1, .triangle 31 2, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle f8fcaf29d4a189f6bf1fdeb9d27d391e0dea127da6c6e76e1be9a4a90b903b7b; original global index 19417.
def localCycle00137 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 2, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle f9cf27dc9314ee6f3e076c7bd7320c347a2305cc0dcb678db2a766cd24b46e4f; original global index 19481.
def localCycle00138 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 2, .triangle 4 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle fb6a793277cde40d8a509c19eed3303b3e2b42143e40d8138bb0a7fea4c3e519; original global index 19625.
def localCycle00139 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .gapLower 2 3, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle fef47a891689ad5c12d346067a8dc5e9abb7aa82456abc734a28e0435dce06fe; original global index 19934.
def localCycle00140 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle ff9f15791271ec5289b9b551c89ac21878cd00f301bce0b9c3a2cf002e6f31c6; original global index 19991.
def localCycle00141 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 33 1, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Original cycle ffcdbe7aeded41e874016fa58b8c2ea9cacbe409394e364f6ef1cc8aa451d733; original global index 20009.
def localCycle00142 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

def library : Library := fun id => if id < 71 then (if id < 35 then (if id < 17 then (if id < 8 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none)))) else (if id < 12 then (if id < 10 then (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none)) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))) else (if id < 14 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)))))) else (if id < 26 then (if id < 21 then (if id < 19 then (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none))))) else (if id < 30 then (if id < 28 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none)) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))) else (if id < 32 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none))))))) else (if id < 53 then (if id < 44 then (if id < 39 then (if id < 37 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none)) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))) else (if id < 41 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none))))) else (if id < 48 then (if id < 46 then (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none)) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none))) else (if id < 50 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)))))) else (if id < 62 then (if id < 57 then (if id < 55 then (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none))) else (if id < 59 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none)) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none))))) else (if id < 66 then (if id < 64 then (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none)) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none))) else (if id < 68 then (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)))))))) else (if id < 107 then (if id < 89 then (if id < 80 then (if id < 75 then (if id < 73 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none))) else (if id < 77 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none))))) else (if id < 84 then (if id < 82 then (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none)) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none))) else (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)))))) else (if id < 98 then (if id < 93 then (if id < 91 then (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none)) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none))) else (if id < 95 then (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none))))) else (if id < 102 then (if id < 100 then (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none)) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none))) else (if id < 104 then (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none)) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none))))))) else (if id < 125 then (if id < 116 then (if id < 111 then (if id < 109 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none))) else (if id < 113 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none)) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none))))) else (if id < 120 then (if id < 118 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none)) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none))) else (if id < 122 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)))))) else (if id < 134 then (if id < 129 then (if id < 127 then (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none)) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none))) else (if id < 131 then (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none))))) else (if id < 138 then (if id < 136 then (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none)) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none))) else (if id < 140 then (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 6, 0, 2, 1], ![4, 3, 5, 0, 2, 1]], proof := .tail 140 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2176)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![6, 5, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 3, 0, 2, 1], ![4, 5, 3, 0, 2, 1]], proof := .tail 4 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2177)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![6, 5, 0, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 3, 0, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 23 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2178)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 2, 1], ![4, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 5]], proof := .tail 91 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2179)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 6, 5, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 2, 1], ![4, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 5, 1]], proof := .tail 91 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2180)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 2, 1], ![4, 3, 0, 6, 2, 1], ![4, 3, 0, 5, 2, 1]], proof := .tail 39 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2181)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 2, 1], ![4, 3, 6, 0, 2, 1], ![4, 3, 5, 0, 2, 1]], proof := .tail 122 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2182)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![6, 5, 0, 4, 1, 2], ![5, 6, 0, 3, 2, 1], ![4, 6, 3, 0, 2, 1], ![4, 5, 3, 0, 2, 1]], proof := .tail 29 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2183)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![6, 5, 0, 4, 1, 2], ![6, 5, 0, 3, 2, 1], ![6, 4, 3, 0, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 7 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2184)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![5, 6, 0, 4, 2, 1], ![5, 6, 0, 3, 2, 1], ![4, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 5]], proof := .tail 113 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2185)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![5, 6, 0, 4, 2, 1], ![5, 6, 0, 3, 2, 1], ![4, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 5, 1]], proof := .tail 113 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2186)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![5, 6, 0, 4, 2, 1], ![5, 6, 0, 3, 2, 1], ![4, 3, 0, 6, 2, 1], ![4, 3, 0, 5, 2, 1]], proof := .tail 113 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2187)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![5, 6, 0, 4, 2, 1], ![5, 6, 0, 3, 2, 1], ![4, 3, 6, 0, 2, 1], ![4, 3, 5, 0, 2, 1]], proof := .tail 94 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2188)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![6, 5, 0, 4, 2, 1], ![5, 6, 0, 3, 2, 1], ![4, 6, 3, 0, 2, 1], ![4, 5, 3, 0, 2, 1]], proof := .tail 42 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2189)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![6, 5, 0, 4, 2, 1], ![6, 5, 0, 3, 2, 1], ![6, 4, 3, 0, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 28 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2190)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 4, 3, 5, 6], ![4, 0, 1, 2, 5, 6], ![3, 0, 1, 2, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 101 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2191)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 4, 3, 5, 6], ![4, 0, 1, 2, 5, 6], ![3, 0, 1, 2, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 126 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2192)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 4, 3, 5, 6], ![4, 0, 1, 2, 6, 5], ![3, 0, 1, 2, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 117 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2193)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 4, 3, 6, 5], ![4, 0, 1, 2, 6, 5], ![3, 0, 1, 2, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .low6 (![138, 40, 1, 112, 32, 103, 17, 114, 62, 119, 78, 75, 41, 131, 13, 45, 75, 95, 3, 15, 75, 131, 100, 75, 43, 5, 120, 75]) }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2194)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 4, 6, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 0, 1, 2, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 58 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2195)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 6, 4, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 0, 1, 6, 2, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 4, 2]], proof := .tail 60 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2196)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 6, 5], ![0, 1, 4, 3, 6, 5], ![4, 0, 1, 2, 6, 5], ![3, 0, 1, 2, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .low6 (![63, 77, 11, 88, 32, 103, 17, 52, 0, 116, 31, 75, 41, 22, 35, 111, 75, 96, 49, 89, 75, 130, 61, 75, 115, 5, 110, 75]) }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2197)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 6, 5], ![0, 1, 4, 6, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 0, 1, 2, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 3, 2, 4]], proof := .tail 64 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2198)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 6, 5], ![0, 1, 6, 4, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 0, 1, 6, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 3, 4, 2]], proof := .tail 79 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2199)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 6, 3, 5], ![0, 1, 4, 6, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 0, 1, 2, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 1, 2, 4]], proof := .tail 90 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2200)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 6, 3, 5], ![0, 1, 6, 4, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 0, 1, 6, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 1, 4, 2]], proof := .tail 79 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2201)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 4, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 0, 6, 1, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 4, 1, 2]], proof := .tail 87 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2202)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 4, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 0, 6, 1, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 99 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2203)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 4, 5, 3, 6], ![4, 0, 1, 5, 2, 6], ![3, 0, 1, 2, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 123 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2204)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 4, 5, 3, 6], ![4, 0, 1, 5, 2, 6], ![3, 0, 1, 2, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 37 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2205)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 4, 5, 6, 3], ![4, 0, 1, 5, 6, 2], ![3, 0, 1, 2, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 48 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2206)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 4, 5, 6, 3], ![4, 0, 1, 5, 6, 2], ![3, 0, 1, 2, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 56 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2207)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 4, 6, 5, 3], ![4, 0, 1, 5, 6, 2], ![3, 0, 1, 2, 6, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 8 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2208)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 4, 6, 5, 3], ![4, 0, 1, 6, 5, 2], ![3, 0, 1, 2, 6, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 81 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2209)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 6, 4, 5, 3], ![4, 0, 1, 5, 6, 2], ![3, 0, 1, 6, 2, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 4, 2]], proof := .tail 36 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2210)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 6, 4, 5, 3], ![4, 0, 1, 6, 5, 2], ![3, 0, 1, 6, 2, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 4, 2]], proof := .tail 81 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2211)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 6, 5], ![0, 1, 4, 6, 5, 3], ![4, 0, 1, 6, 5, 2], ![3, 0, 1, 2, 6, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 1, 3, 2, 4]], proof := .tail 6 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2212)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 6, 5], ![0, 1, 6, 4, 5, 3], ![4, 0, 1, 6, 5, 2], ![3, 0, 1, 6, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 1, 3, 4, 2]], proof := .tail 71 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2213)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 6, 3, 5], ![0, 1, 4, 6, 5, 3], ![4, 0, 6, 1, 5, 2], ![3, 0, 1, 2, 6, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 1, 2, 4]], proof := .tail 16 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2214)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 6, 3, 5], ![0, 1, 6, 4, 5, 3], ![4, 0, 6, 1, 5, 2], ![3, 0, 1, 6, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 1, 4, 2]], proof := .tail 16 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2215)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 4, 5, 3], ![4, 0, 6, 1, 5, 2], ![3, 0, 6, 1, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 4, 1, 2]], proof := .tail 16 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2216)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 4, 5, 3], ![4, 0, 6, 1, 5, 2], ![3, 0, 6, 1, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 142 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2217)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 5, 4, 3, 6], ![4, 0, 1, 5, 2, 6], ![3, 0, 1, 5, 2, 6], ![0, 1, 3, 4, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 53 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2218)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 5, 4, 6, 3], ![4, 0, 1, 5, 6, 2], ![3, 0, 1, 5, 2, 6], ![0, 1, 3, 4, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 47 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2219)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 5, 6, 4, 3], ![4, 0, 1, 5, 6, 2], ![3, 0, 1, 5, 6, 2], ![0, 1, 3, 4, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 69 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2220)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 6, 5, 4, 3], ![4, 0, 1, 5, 6, 2], ![3, 0, 1, 5, 6, 2], ![0, 1, 3, 4, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 106 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2221)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 6, 5, 4, 3], ![4, 0, 1, 5, 6, 2], ![3, 0, 1, 6, 5, 2], ![0, 1, 3, 6, 4, 2], ![0, 1, 3, 5, 4, 2]], proof := .tail 44 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2222)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 5, 6], ![0, 1, 6, 5, 4, 3], ![4, 0, 1, 6, 5, 2], ![3, 0, 1, 6, 5, 2], ![0, 1, 6, 3, 4, 2], ![0, 1, 5, 3, 4, 2]], proof := .tail 21 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2223)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 3, 6, 5], ![0, 1, 6, 5, 4, 3], ![4, 0, 1, 6, 5, 2], ![3, 0, 1, 6, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 1, 3, 4, 2]], proof := .tail 132 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2224)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 6, 3, 5], ![0, 1, 6, 5, 4, 3], ![4, 0, 6, 1, 5, 2], ![3, 0, 1, 6, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 3, 1, 4, 2]], proof := .tail 135 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2225)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 5, 4, 3], ![4, 0, 6, 1, 5, 2], ![3, 0, 6, 1, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 3, 4, 1, 2]], proof := .tail 102 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2226)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 5, 4, 3], ![4, 0, 6, 1, 5, 2], ![3, 0, 6, 1, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 3, 4, 2, 1]], proof := .tail 102 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2227)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 4, 5, 3, 6], ![4, 0, 5, 1, 2, 6], ![3, 0, 1, 2, 5, 6], ![0, 3, 1, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 74 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2228)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 4, 5, 3, 6], ![4, 0, 5, 1, 2, 6], ![3, 0, 1, 2, 6, 5], ![0, 3, 1, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 105 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2229)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 4, 5, 6, 3], ![4, 0, 5, 1, 6, 2], ![3, 0, 1, 2, 5, 6], ![0, 3, 1, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 27 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2230)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 4, 5, 6, 3], ![4, 0, 5, 1, 6, 2], ![3, 0, 1, 2, 6, 5], ![0, 3, 1, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 27 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2231)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 4, 6, 5, 3], ![4, 0, 5, 1, 6, 2], ![3, 0, 1, 2, 6, 5], ![0, 3, 1, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 30 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2232)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 6, 4, 5, 3], ![4, 0, 5, 1, 6, 2], ![3, 0, 1, 6, 2, 5], ![0, 3, 1, 6, 2, 4], ![0, 1, 3, 5, 4, 2]], proof := .tail 129 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2233)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 5, 6, 3], ![0, 1, 4, 5, 6, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 1, 2, 5, 6], ![0, 3, 1, 2, 4, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 141 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2234)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 5, 6, 3], ![0, 1, 4, 5, 6, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 1, 2, 6, 5], ![0, 3, 1, 2, 6, 4], ![0, 3, 1, 2, 5, 4]], proof := .tail 139 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2235)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 5, 6, 3], ![0, 1, 4, 6, 5, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 1, 2, 6, 5], ![0, 3, 1, 6, 2, 4], ![0, 3, 1, 5, 2, 4]], proof := .tail 8 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2236)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 5, 6, 3], ![0, 1, 6, 4, 5, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 1, 6, 2, 5], ![0, 3, 1, 6, 2, 4], ![0, 3, 1, 5, 4, 2]], proof := .tail 36 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2237)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 6, 5, 3], ![0, 1, 4, 6, 5, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 1, 2, 6, 5], ![0, 3, 6, 1, 2, 4], ![0, 3, 5, 1, 2, 4]], proof := .tail 76 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2238)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 6, 5, 3], ![0, 1, 6, 4, 5, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 1, 6, 2, 5], ![0, 3, 6, 1, 2, 4], ![0, 3, 5, 1, 4, 2]], proof := .tail 36 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2239)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 4, 5, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 6, 1, 2, 5], ![0, 3, 6, 1, 2, 4], ![0, 3, 5, 4, 1, 2]], proof := .tail 2 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2240)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 4, 5, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 6, 1, 2, 5], ![0, 3, 6, 1, 2, 4], ![0, 3, 5, 4, 2, 1]], proof := .tail 109 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2241)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 6, 5, 3], ![0, 1, 4, 6, 5, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 1, 2, 6, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 3, 1, 2, 4]], proof := .tail 92 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2242)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 6, 5, 3], ![0, 1, 6, 4, 5, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 1, 6, 2, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 3, 1, 4, 2]], proof := .tail 92 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2243)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 4, 5, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 6, 1, 2, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 3, 4, 1, 2]], proof := .tail 92 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2244)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 4, 5, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 6, 1, 2, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 107 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2245)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 5, 4, 3, 6], ![4, 0, 5, 1, 2, 6], ![3, 0, 1, 5, 2, 6], ![0, 3, 1, 4, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 68 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2246)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 5, 4, 6, 3], ![4, 0, 5, 1, 6, 2], ![3, 0, 1, 5, 2, 6], ![0, 3, 1, 4, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 27 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2247)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 5, 6, 4, 3], ![4, 0, 5, 1, 6, 2], ![3, 0, 1, 5, 6, 2], ![0, 3, 1, 4, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 124 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2248)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 6, 5, 4, 3], ![4, 0, 5, 1, 6, 2], ![3, 0, 1, 5, 6, 2], ![0, 3, 1, 4, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 73 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2249)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 5, 3, 6], ![0, 1, 6, 5, 4, 3], ![4, 0, 5, 1, 6, 2], ![3, 0, 1, 6, 5, 2], ![0, 3, 1, 6, 4, 2], ![0, 1, 3, 5, 4, 2]], proof := .tail 18 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2250)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 5, 6, 3], ![0, 1, 5, 4, 6, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 1, 5, 2, 6], ![0, 3, 1, 4, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 72 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2251)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 5, 6, 3], ![0, 1, 5, 6, 4, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 1, 5, 6, 2], ![0, 3, 1, 4, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 85 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2252)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 5, 6, 3], ![0, 1, 6, 5, 4, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 1, 5, 6, 2], ![0, 3, 1, 4, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 106 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2253)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 5, 6, 3], ![0, 1, 6, 5, 4, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 1, 6, 5, 2], ![0, 3, 1, 6, 4, 2], ![0, 3, 1, 5, 4, 2]], proof := .tail 108 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2254)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 6, 5, 3], ![0, 1, 6, 5, 4, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 1, 6, 5, 2], ![0, 3, 6, 1, 4, 2], ![0, 3, 5, 1, 4, 2]], proof := .tail 55 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2255)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 5, 4, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 6, 1, 5, 2], ![0, 3, 6, 1, 4, 2], ![0, 3, 5, 4, 1, 2]], proof := .tail 12 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2256)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 5, 4, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 6, 1, 5, 2], ![0, 3, 6, 1, 4, 2], ![0, 3, 5, 4, 2, 1]], proof := .tail 12 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2257)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 4, 6, 5, 3], ![0, 1, 6, 5, 4, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 1, 6, 5, 2], ![0, 6, 3, 1, 4, 2], ![0, 5, 3, 1, 4, 2]], proof := .tail 9 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2258)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 5, 4, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 6, 1, 5, 2], ![0, 6, 3, 1, 4, 2], ![0, 5, 3, 4, 1, 2]], proof := .tail 57 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2259)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 5, 4, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 6, 1, 5, 2], ![0, 6, 3, 1, 4, 2], ![0, 5, 3, 4, 2, 1]], proof := .tail 57 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2260)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 4, 3, 6], ![4, 0, 5, 1, 2, 6], ![3, 0, 5, 1, 2, 6], ![0, 3, 4, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 66 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2261)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 4, 6, 3], ![4, 0, 5, 1, 6, 2], ![3, 0, 5, 1, 2, 6], ![0, 3, 4, 1, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 51 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2262)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 6, 4, 3], ![4, 0, 5, 1, 6, 2], ![3, 0, 5, 1, 6, 2], ![0, 3, 4, 1, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 80 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2263)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 6, 5, 4, 3], ![4, 0, 5, 1, 6, 2], ![3, 0, 5, 1, 6, 2], ![0, 3, 4, 1, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 46 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2264)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 4, 6, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 5, 1, 2, 6], ![0, 3, 4, 1, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 19 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2265)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 6, 4, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 5, 1, 6, 2], ![0, 3, 4, 1, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 118 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2266)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 6, 5, 4, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 5, 1, 6, 2], ![0, 3, 4, 1, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 46 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2267)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 5, 6, 1, 2], ![0, 3, 4, 1, 2, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 10 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2268)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 5, 6, 1, 2], ![0, 3, 4, 1, 6, 2], ![0, 3, 4, 1, 5, 2]], proof := .tail 106 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2269)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 5, 6, 1, 2], ![0, 3, 4, 6, 1, 2], ![0, 3, 4, 5, 1, 2]], proof := .tail 26 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2270)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 6, 5, 1, 2], ![0, 3, 6, 4, 1, 2], ![0, 3, 5, 4, 1, 2]], proof := .tail 134 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2271)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 5, 6, 1, 2], ![0, 3, 4, 6, 1, 2], ![0, 3, 4, 5, 2, 1]], proof := .tail 84 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2272)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 6, 5, 1, 2], ![0, 3, 6, 4, 1, 2], ![0, 3, 5, 4, 2, 1]], proof := .tail 83 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2273)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 6, 5, 1, 2], ![0, 6, 3, 4, 1, 2], ![0, 5, 3, 4, 1, 2]], proof := .tail 93 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2274)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 6, 5, 1, 2], ![0, 6, 3, 4, 1, 2], ![0, 5, 3, 4, 2, 1]], proof := .tail 93 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2275)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 4, 3, 6], ![4, 0, 5, 1, 2, 6], ![3, 0, 5, 1, 2, 6], ![0, 3, 4, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 59 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2276)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 4, 6, 3], ![4, 0, 5, 1, 6, 2], ![3, 0, 5, 1, 2, 6], ![0, 3, 4, 2, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 121 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2277)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 6, 4, 3], ![4, 0, 5, 1, 6, 2], ![3, 0, 5, 1, 6, 2], ![0, 3, 4, 2, 1, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 14 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2278)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 4, 6, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 5, 1, 2, 6], ![0, 3, 4, 2, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 121 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2279)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 6, 4, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 5, 1, 6, 2], ![0, 3, 4, 2, 1, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 136 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2280)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 5, 6, 1, 2], ![0, 3, 4, 2, 1, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 121 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2281)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 5, 6, 1, 2], ![0, 3, 4, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 33 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2282)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 5, 6, 1, 2], ![0, 3, 4, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 65 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2283)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 5, 6, 1, 2], ![0, 3, 4, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 50 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2284)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![4, 0, 5, 6, 1, 2], ![3, 0, 6, 5, 1, 2], ![0, 3, 6, 4, 2, 1], ![0, 3, 5, 4, 2, 1]], proof := .tail 24 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2285)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 6, 5, 1, 2], ![0, 6, 3, 4, 2, 1], ![0, 5, 3, 4, 2, 1]], proof := .tail 86 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2286)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 3, 5, 6], ![4, 0, 1, 2, 5, 6], ![3, 0, 2, 1, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 104 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2287)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 3, 5, 6], ![4, 0, 1, 2, 5, 6], ![3, 0, 2, 1, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 128 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2288)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 3, 5, 6], ![4, 0, 1, 2, 6, 5], ![3, 0, 2, 1, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 34 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2289)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 3, 6, 5], ![4, 0, 1, 2, 6, 5], ![3, 0, 2, 1, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 98 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2290)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 3, 6, 5], ![0, 4, 1, 3, 6, 5], ![4, 0, 1, 2, 6, 5], ![3, 0, 2, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .tail 98 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2291)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 6, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 0, 2, 1, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 125 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2292)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 3, 6, 5], ![0, 4, 1, 6, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 0, 2, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 3, 2, 4]], proof := .tail 25 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2293)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 6, 3, 5], ![0, 4, 1, 6, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 0, 2, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 1, 2, 4]], proof := .tail 137 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2294)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 6, 2, 3, 5], ![0, 4, 6, 1, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 0, 2, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 2, 1, 4]], proof := .tail 54 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2295)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 2, 3, 5], ![0, 4, 6, 1, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 0, 2, 6, 1, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 2, 4, 1]], proof := .tail 97 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2296)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 4, 2, 3, 5], ![0, 6, 4, 1, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 0, 6, 2, 1, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 20 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2297)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 5, 3, 6], ![4, 0, 1, 5, 2, 6], ![3, 0, 2, 1, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 82 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2298)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 5, 3, 6], ![4, 0, 1, 5, 2, 6], ![3, 0, 2, 1, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 67 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2299)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 5, 6, 3], ![4, 0, 1, 5, 6, 2], ![3, 0, 2, 1, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 70 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2300)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 5, 6, 3], ![4, 0, 1, 5, 6, 2], ![3, 0, 2, 1, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 127 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2301)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 6, 5, 3], ![4, 0, 1, 5, 6, 2], ![3, 0, 2, 1, 6, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 133 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2302)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 6, 5, 3], ![4, 0, 1, 6, 5, 2], ![3, 0, 2, 1, 6, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 38 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2303)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (2176 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 2176 ≤ id.val) (hhigh : id.val < 2304) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 2176)) = true := by
  let j : Fin 128 := ⟨id.val - 2176, by omega⟩
  have hsum : 2176 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (2176 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard017
