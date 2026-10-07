import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard086
open N4R2RowDataReplay

-- Original cycle 007d6440b2905b58691701b26ec54a9a27b541f87c973aaf5e7faf73c2120e12; original global index 44.
def localCycle00000 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 1 5, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 5 2, .triangle 17 1, .gapUpper 2 3, .gapLower 0 4]

-- Original cycle 00ba3745facf56694ead5544668bdd24a549d413bd22e7b815fafde4fd281f96; original global index 66.
def localCycle00001 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 30 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 025cf5db4b9108a16f09c518d1f62ef6108b5f62a4dd5bfb16ec68747d39be1f; original global index 187.
def localCycle00002 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .gapLower 6 1, .triangle 30 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 034f2043f196e3164488133305ef192171472013c33f42284a328621c7bac50e; original global index 266.
def localCycle00003 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 4 3, .triangle 34 1, .triangle 14 0, .gapLower 0 2]

-- Original cycle 038b353b0f181ef7b33161406da76109ff76ca0e37060138cafe84d4f5c45de3; original global index 286.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 2, .triangle 12 1, .triangle 13 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 04073e36c07cc7f7cfb33c5b50df1c4841055546883593b3b6f85645ba2f000e; original global index 317.
def localCycle00005 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 1 5, .distance 0 1]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 3, .triangle 3 1, .gapUpper 1 3]

-- Original cycle 0428281dab98ad6fa45914d4c0d8b7937db34f77897d2a97454340ddb3236922; original global index 326.
def localCycle00006 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 0 0, .triangle 2 0, .triangle 23 0, .triangle 29 0, .gapLower 4 0]

-- Original cycle 04f8b2ef7aeda52659761a3e3ef3f4f26e6668c67c4b8374589259f90935c0ab; original global index 397.
def localCycle00007 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 1]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 1 3, .gapLower 6 3, .triangle 4 1]

-- Original cycle 055f6c60b6c5e05704a2ea42625dcbc9bc58675030491d28c22d9a56b297bd37; original global index 434.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -2, -2, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .gapLower 6 2, .triangle 4 1, .triangle 3 0, .triangle 17 1, .triangle 28 1, .gapLower 4 0]

-- Original cycle 05f25becb20822bc4aadd8b17606b2774e8836ebed5036cbf4e39e9a0da31652; original global index 494.
def localCycle00009 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 8 2, .gapLower 6 1, .gapUpper 2 4]

-- Original cycle 05fabd79e77e717ccc49fe2e219c9a2a8e440d280c4748627f3211662cb97e7b; original global index 498.
def localCycle00010 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 06cf9950f712a612160bdf709685ec32e6629f724cfab4b64efd3d21ed8468c3; original global index 561.
def localCycle00011 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 6, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, 0, -2, -2, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.triangle 7 2, .triangle 14 2, .gapLower 6 2, .gapLower 6 1, .gapUpper 2 4]

-- Original cycle 08a833e2e098672a1f51d892c1d9b5d3f2fe102381fade86b9716fee6886b655; original global index 691.
def localCycle00012 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .triangle 21 2, .gapLower 6 2, .triangle 8 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 09a568a8a961ff98ea8e97066f39e730718fb4ca2ae57e8cd09799d7ce92698b; original global index 770.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 4 1, .triangle 3 0, .triangle 17 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 0a1815b80555f571cec55a99d01ef283033d8e472e4159c3f01265f97aa07ca4; original global index 814.
def localCycle00014 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 3 4]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 3 4, .gapUpper 5 5, .gapLower 6 5, .triangle 32 0]

-- Original cycle 0ab32c0d6baa47565f5c125a164c61aaa8fa967caa99362da3e1ea86ce143406; original global index 851.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 22 2, .triangle 3 0, .triangle 4 0, .triangle 18 1, .triangle 30 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 0b3943b63bdd84adf2531174d354404678ae0f891c1f388b9ae0015071ef84f2; original global index 898.
def localCycle00016 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 3 6, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 32 1]

-- Original cycle 0b3a2a35fea42c56034ca19059b5f8c7d6ccda563b9c8ec64738479c1c18a08d; original global index 900.
def localCycle00017 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .gapLower 6 2, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle 0cfd0fbe4ce38c75ff60c9e1f6ed105c37377548f759c38580006736c912ac16; original global index 1027.
def localCycle00018 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 0, .triangle 31 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 0d45d9bd2d7bb3efbd964e8e93abd74091e18e83a187214aada94438dbb65748; original global index 1051.
def localCycle00019 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 3]
    constant := ![2, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 23 2, .gapLower 6 3, .triangle 11 1]

-- Original cycle 0d7e473311ff4725dcd6ef3f73dc5c179dadbfd4b4eac92ba08ca2f343273231; original global index 1067.
def localCycle00020 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 4, .distance 2 4, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 0 1, .triangle 2 0, .triangle 16 1, .gapLower 4 0]

-- Original cycle 0ec30e11fc4eaf6f681d2b0ae854c8b69a0367b90d0cd763db4f7fa2bf7c0026; original global index 1167.
def localCycle00021 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, 0, -2, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 30 0, .gapLower 2 2, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 0fba38ff71d6b1a5977dfbec782733c1d9f5c2139001462bb7a60d930de848e3; original global index 1255.
def localCycle00022 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 2 2, .gapUpper 4 3, .gapLower 6 4, .triangle 4 0]

-- Original cycle 0ffc317e7aa5e17776f82f93b59f9857bb6738854bef42107e9fd7d001f5e077; original global index 1276.
def localCycle00023 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 1 5, .distance 0 1]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 5 2, .gapUpper 1 3]

-- Original cycle 10db90966c1fc5f58c0a8f22addaebff366241efd4f52f9f6008268c403d438c; original global index 1351.
def localCycle00024 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 0 1, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 129e1edec5787627a29c9cff44bfbcc50cc5a7ba436a7621cbac55296005543d; original global index 1472.
def localCycle00025 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle 14bc497eff1729289a3cabdcccbcb3a4398097195d812f69b6439ee5770ed1d6; original global index 1643.
def localCycle00026 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 13 2, .gapLower 6 1, .corridorLower 2 6, .thetaLower 2]

-- Original cycle 150443d538bc9a24117582446a6bdc480d880ee1f4ecdaa790fed3849ec63050; original global index 1668.
def localCycle00027 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .theta 4]
    constant := ![3, 0, -2, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .triangle 2 0, .triangle 16 1, .gapLower 4 0]

-- Original cycle 15e96c7567f2f4c47b5bec663aef748a58a46a2371af636475b2d26c91103265; original global index 1736.
def localCycle00028 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 3 0, .triangle 4 0, .triangle 24 1, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle 16117113c51168b5f860e29f17c4ab55839254b3671c4acf41589f8ea8b8927d; original global index 1745.
def localCycle00029 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 1617941c34b3f7a2912c6befdd02e3f98b6c0dfd7725c943bcfcd40c5d876be9; original global index 1746.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 2, .gapLower 6 2, .triangle 8 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 16a240a63c007920c486f6fee79f703fa7b226d6ee9bb47736364f65b1342651; original global index 1774.
def localCycle00031 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 3 5]
    constant := ![2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, true] }
  origin := ![.gapUpper 5 5, .triangle 34 2, .gapLower 6 4, .triangle 33 1]

-- Original cycle 16ae71469ec0d56ff02a8f0b59ceecc32e896ff0a7eaf6c5e7b7de3fa69879dd; original global index 1779.
def localCycle00032 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 5, .distance 0 4, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .gapLower 0 3, .gapLower 0 2, .gapLower 4 2, .triangle 16 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 16f55965705fd74e75849958c6582e6209bdeab7cc5b90182f3a0a1ad930cc1a; original global index 1805.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .gapLower 6 1, .corridorLower 2 6, .thetaLower 2]

-- Original cycle 1874005b9ab5c9f133ed6b58d2b6a89535d4d4741074b564da795405dbdd67da; original global index 1915.
def localCycle00034 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 3, .gapLower 6 3, .triangle 14 1]

-- Original cycle 19860960256f91539ee17f7b5f56dc34262f814ab1f5c5c4f51a5d43cbed1846; original global index 1992.
def localCycle00035 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .triangle 14 1, .triangle 12 1, .triangle 9 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 19892eed1331d4f565069d843532d776ba423a5eba138ce6fa892f402515b1e2; original global index 1994.
def localCycle00036 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 21 2, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 19cbf63a9cdc9ef180856ae64e124294056c9944a45b8af5faff13d5815cd8b9; original global index 2012.
def localCycle00037 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .gapLower 6 1, .triangle 30 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 1a99d4b966fdff1e815556a43b763ef3372fb9ce6fe251b6803c00b4deb4a428; original global index 2069.
def localCycle00038 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, -2, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .gapUpper 3 6, .thetaLower 3]

-- Original cycle 1b796d83e36c4307d8519a0a3b74325fff3297208345692e42114d4077602a2d; original global index 2127.
def localCycle00039 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 0 6, .distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 13 2, .gapLower 0 4, .triangle 3 2, .triangle 12 1, .triangle 9 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 1bdc43221d09ab95f14e9a118c6f7ab7c8def8c575aa18e51342828f0d40f795; original global index 2155.
def localCycle00040 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 0 3, .gapUpper 5 3, .triangle 24 2, .triangle 4 0]

-- Original cycle 1d033cb0dfc47aedf24f2a650ad2368a23ee8376e4bbbee100b4a0a16e3b92e5; original global index 2235.
def localCycle00041 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, 0, -2, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .triangle 14 1, .triangle 30 0, .gapLower 2 2, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 1d2b69aa70d4cc80d4f95d1c0aec3d36c66ff64055573af8e549fbbbca89d6d2; original global index 2251.
def localCycle00042 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 2, .triangle 14 1, .gapLower 0 2, .gapLower 0 1, .gapLower 3 2, .triangle 15 1, .corridorLower 2 3]

-- Original cycle 1d690b0818b15862bf051c387340394286c2e85aeedb1090ec7d0960f3472930; original global index 2265.
def localCycle00043 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .gapLower 5 3, .triangle 17 0, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 1f2086ba4b85ab33540f22d514250978e019e158fce2037d563e51ef304e5a5a; original global index 2390.
def localCycle00044 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 6, .distance 0 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 14 2, .gapLower 0 3, .triangle 10 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 22135820091e9d0ee58e1c385a7a8f82838f5f50d5ea643e94d6783db242cb03; original global index 2609.
def localCycle00045 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 5, .distance 2 5, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 24 2, .gapLower 6 2, .triangle 4 1, .triangle 3 0, .triangle 17 1, .gapLower 5 0]

-- Original cycle 224dfc5a0bf9b5f9fa94ca61de6b956990255adb9d29c64ba7ed0611139fbbc4; original global index 2629.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .triangle 12 0, .triangle 9 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 231cbb8bb584e487ab641864c1d4b9c3f7b9e645e5c5673f879a606efdd4a4ee; original global index 2697.
def localCycle00047 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 5, .distance 0 4, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -2, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .triangle 14 1, .gapLower 0 2, .gapLower 4 2, .triangle 16 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 245e677fb9facb0ebd0e3f5ed88eb282946bb878fc80e17d3ae583b5a388fb65; original global index 2788.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -3, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .triangle 4 0, .gapLower 1 3, .gapLower 5 1, .triangle 28 1, .gapLower 4 0]

-- Original cycle 24769bde0ccba42f292df67b4fc1a1a9d023c1b0bec257dec5598066c3ac6beb; original global index 2797.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 11 2, .gapLower 6 1, .corridorLower 2 6, .thetaLower 2]

-- Original cycle 24a65766f94bcedc5de7965873fc299c4bed3c9bb36f74411b86ea96d89bb883; original global index 2811.
def localCycle00050 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 4 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .gapLower 6 4, .triangle 13 2, .triangle 8 1, .gapLower 6 0]

-- Original cycle 24ffa6a399d602cfbd00f45b64902ed381e89bb8c77c343be24a05f30f174f92; original global index 2838.
def localCycle00051 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 6, .distance 0 5, .distance 0 4, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -2, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .gapLower 0 4, .triangle 14 1, .gapLower 0 2, .gapLower 4 2, .triangle 16 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 2532e8ea05cadb8d855050f3267f02b53955c6319a244de472ea6a0b34f1a0e0; original global index 2857.
def localCycle00052 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.gapUpper 3 3, .triangle 33 1, .triangle 34 0, .triangle 12 0, .triangle 9 1]

-- Original cycle 25512b7d655d3d078c405dba0c63b578338f8e2e4c732f895a798440bf680d13; original global index 2868.
def localCycle00053 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 8 1, .gapUpper 2 4]

-- Original cycle 25d69ff540d01efee175fe22e9fd569c2aace348371d81a6f1e67684cf64ce7d; original global index 2905.
def localCycle00054 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 4, .distance 0 3]
    constant := ![2, 0, 0, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, true, false] }
  origin := ![.gapUpper 3 3, .triangle 11 2, .triangle 13 1, .gapLower 0 1]

-- Original cycle 266db30532de8b210c27078de6150591e2122fc55fe4fa0870643bcd3d33ffe2; original global index 2949.
def localCycle00055 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 6, .distance 2 6, .distance 0 2, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 2, .triangle 18 1, .triangle 8 0, .triangle 0 1, .triangle 3 0, .triangle 17 1, .triangle 28 1, .gapLower 4 0]

-- Original cycle 2675d10c15909d9c0bdf526e04be0eb30873a53b9f56d8d4bfc08ce4fe5fcb6d; original global index 2953.
def localCycle00056 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -2, 0, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .triangle 4 1, .triangle 3 0, .triangle 17 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 26d15faef9d2aa867580f358ec9f2a3c5e84b363df23f933f1602d8f7c8885df; original global index 2973.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 30 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 27470daf8429bec2a29b851a5d85b4e071485ce4bfa93682ec08b16d5f74c4f4; original global index 3005.
def localCycle00058 : Cycle where
  length := 5
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 1, .distance 0 6, .distance 0 5, .theta 0]
    constant := ![2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 0 1, .triangle 4 2, .gapLower 0 3, .corridorLower 0 5]

-- Original cycle 274bfe138d77bf555efd6cac632d312dfea411545eeec0285cb06d7d7f24bd33; original global index 3009.
def localCycle00059 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 3 3, .triangle 32 1, .triangle 13 0, .gapLower 0 1]

-- Original cycle 28567738ccea9f79cd3f0ad477126fb12aa6e3eb4f13c50f1247153d8f222e07; original global index 3094.
def localCycle00060 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 287ebcfa86ef467476633cb2a2193d4cc6a318dc2023126a9ba7e6f31ac0a3cd; original global index 3102.
def localCycle00061 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 3 5]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 33 1]

-- Original cycle 28c0b2bfa8d75e6f1412496546711f93732975b5cd59de1412f9d5fcb513a19f; original global index 3120.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 2, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0]
    constant := ![2, -2, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 0 1, .triangle 3 0, .triangle 22 1, .triangle 19 1, .corridorLower 1 3, .thetaNext 0]

-- Original cycle 293c1260782dbac41bc6f870c02e5d1b308fdae87d9eceb8259f80fbc09dfad3; original global index 3147.
def localCycle00063 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 29451940ab5a8930e620a63e8dd7272b8118c1933a7529464e8bbf95d64dd830; original global index 3152.
def localCycle00064 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, 0, -1, -2, 3, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, -1, 0]
    strict := ![false, true, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapUpper 3 6, .thetaNext 2]

-- Original cycle 296274eeba13de3b80ac9facebd677b7cb93c4020528aa653533b141b4092b0e; original global index 3156.
def localCycle00065 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 3]
    constant := ![4, -1, -2, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 3 6, .triangle 32 0, .gapLower 6 3, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .gapLower 3 0]

-- Original cycle 2b0332932a1c2375614d14d880ca28a4e46b549eba919b25b1197f15f0c6f931; original global index 3283.
def localCycle00066 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -2, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 3, .gapLower 6 3, .triangle 14 1]

-- Original cycle 2bd05087648ac0beef5ff2b9b5b24767f9b5ff1c7ada4c744327f911ebd649bd; original global index 3353.
def localCycle00067 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 3]
    constant := ![2, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .triangle 4 2, .triangle 11 1]

-- Original cycle 2cef8951fa034efe0a1620025036055a239cfad34b5b691b25298ca284818b79; original global index 3432.
def localCycle00068 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 5 4, .triangle 12 0, .gapLower 0 1]

-- Original cycle 2dcf50005522d028994309989c0a02361bd800a7abe05dbd29bcf750d4fb7950; original global index 3497.
def localCycle00069 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, 0, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 2eab4cf0f97ef360df4bf4a420182ab5385c773830b30ba787aa9a624e848e73; original global index 3568.
def localCycle00070 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 2eed69d6991fddb8c9e6d829183aea191d1b3a55a901e07d91eecf3df201e5bd; original global index 3591.
def localCycle00071 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 27 1, .corridorLower 2 3]

-- Original cycle 2fb1719afc84402ca391dfd9a686c2a3523e1563ec45d821587dc734e2419240; original global index 3644.
def localCycle00072 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 0 0, .triangle 2 0, .triangle 16 1, .gapLower 4 0]

-- Original cycle 2fb229b74baac37f2175a512b209eba0cea1a6418b73df83a853a0bfbe63382c; original global index 3645.
def localCycle00073 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 3 6, .distance 5 6, .distance 3 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 33 2, .gapLower 6 4, .gapUpper 5 4]

-- Original cycle 3012eddb4aabf998798830a98af90c692263aee94c45999206cdd2e38777113f; original global index 3664.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 2 6, .distance 0 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 30 2, .triangle 8 0, .triangle 0 1, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 32d08bd6f7d2ab9183b236cd3b92e1d51468736a09a171f7004d8edd49c0b828; original global index 3892.
def localCycle00075 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 0 5, .distance 0 4]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 4 3, .gapLower 5 3, .gapLower 0 2]

-- Original cycle 32e03c8f8b41946b568970b12647c2384032fc29f31d135d4cb9579544255188; original global index 3897.
def localCycle00076 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 14 2, .gapLower 6 2, .triangle 18 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 340e839321fece43c7106eef6930b48ef76a146f2d29db0456624cd38abcabae; original global index 3989.
def localCycle00077 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 3414eb90576984ff11aa9b321096d95cf7a643da552a5c45dfd780adbbb0244b; original global index 3992.
def localCycle00078 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, 0, -3, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapUpper 3 6, .thetaLower 3]

-- Original cycle 341a699761df31ef98789450b01d37a4d8ac56270a0d746513e3bfd0916f57c8; original global index 3995.
def localCycle00079 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 4, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 22 2, .triangle 24 0, .triangle 14 0, .triangle 3 1, .triangle 2 0, .triangle 16 1, .gapLower 4 0]

-- Original cycle 347438300011b8fe1c7eb220df6228b3357048a43e5b925e11c78ceb1ff3d7ae; original global index 4016.
def localCycle00080 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -2, 2, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .gapLower 6 6, .triangle 33 0, .triangle 20 2, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 34e5c438e6a899edcaa504ff444da90cfb91a99470e381575e076bfa9a836f1d; original global index 4046.
def localCycle00081 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -2, -1, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 8 2, .gapLower 0 4, .triangle 3 0, .triangle 17 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 35eaf988da26314fa1e0ef20c965da8df6787e69a40d980b03a9ab4d5c3c0080; original global index 4138.
def localCycle00082 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .gapLower 6 3, .triangle 4 2, .triangle 8 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 37886621c794420b262ba31e47a4aae1df9974a9758bde642927ba518dcec246; original global index 4270.
def localCycle00083 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 0 6, .distance 0 1]
    constant := ![-2, 2, 0, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 0 3, .gapUpper 5 3, .triangle 14 2, .gapLower 0 4]

-- Original cycle 393f5dce4c35096d60baa06bd8dfa71374b39ca36f6518231c17a82160d4651c; original global index 4404.
def localCycle00084 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 4 6, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 34 1]

-- Original cycle 3a1b5080ddc181638e66bbe3dfa71203cd57c422479b23c9b5dba227c233d569; original global index 4483.
def localCycle00085 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 3a264baf04dbe3869b11bc952e3f9d6f313c6ac27e3ad3c90455edf4905e94bb; original global index 4490.
def localCycle00086 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 0 0, .triangle 2 2, .triangle 13 0, .triangle 29 0, .gapLower 4 0]

-- Original cycle 3a4c2ce0936b49d5bd8089f9de5f2e0e11403c9534642cd2759a1f0a029a6121; original global index 4501.
def localCycle00087 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 3a55b61e0191e582c2b6fa637b14fc46a597a9c89a65caa440be4a5f20198e8e; original global index 4505.
def localCycle00088 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 0 0, .triangle 2 0, .triangle 16 1, .gapLower 4 0]

-- Original cycle 3b566a170195cf222b3974311dcd1008f2f85c335f130b26277de6e054bb09a4; original global index 4586.
def localCycle00089 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 3 2, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 3bf3f608741409aa40a5730953a3be5d1574adc3f7d7bedd77ff3505154c807d; original global index 4646.
def localCycle00090 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 0 5, .distance 0 4]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 4 3, .gapLower 5 3, .gapLower 0 2]

-- Original cycle 3e4d1bf524bf9521241b38f15345cd252a1189de526ce9ff7f65288e2cced2ba; original global index 4819.
def localCycle00091 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 2, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 3efede6e8e8317abbfcd574a34f9c561759929b6504ac4f63b1a3ecdd71d4fb0; original global index 4869.
def localCycle00092 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .gapLower 0 3, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 3f748b1fcd46db2bf6b6047cb1f1b906214a36925a564c32092bdc3f511d82ec; original global index 4902.
def localCycle00093 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 1]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 1 4, .triangle 4 2, .gapLower 0 4]

-- Original cycle 405e5d0ff732911419f47f03210bb6b792eef26589660ca0fc5be597fb1f109d; original global index 4976.
def localCycle00094 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 22 2, .triangle 3 2, .triangle 14 0, .triangle 30 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 4180d191a32c7ee3e0fa83a009eb4e522aa5e7e76500939c3e0c41246948f3f4; original global index 5053.
def localCycle00095 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .gapLower 6 2, .triangle 4 1, .triangle 3 0, .triangle 17 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 41c0390d7ac8bf62317972b29b691c8afdd0829431f44891e43029c896c19edd; original global index 5071.
def localCycle00096 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 1, .distance 0 5, .distance 1 5, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -2, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .triangle 4 1, .gapLower 0 3, .gapLower 5 2, .triangle 17 1, .triangle 26 1, .corridorLower 2 3]

-- Original cycle 41c60043389ac7c79ebb4ae5c2a8198f22ffd464806dba26d202f138388cd6c9; original global index 5075.
def localCycle00097 : Cycle where
  length := 4
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 1, .distance 0 5, .theta 0]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 0 1, .gapLower 0 3, .corridorLower 0 5]

-- Original cycle 4213504f387972f6bf4191abea74d0e6ec2a0142a2e7c5aa6451954236976aef; original global index 5091.
def localCycle00098 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 21 2, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 43d039b1a0b5d72127c810d2c2f0680fac69b7ca36f8f3c47321b0b2c8a7f13f; original global index 5247.
def localCycle00099 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 4 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 13 2, .gapLower 6 2, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 4456ee5e08c14b1bc941ad5357b891bba9f08d9f740fbed321f072c74f98cbbe; original global index 5291.
def localCycle00100 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 2, .triangle 4 2, .gapLower 6 1, .gapLower 6 0]

-- Original cycle 45a3d4fe5a956eee62a42771be9e86d43a512664282ba7332807b74f5f749b95; original global index 5387.
def localCycle00101 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 0 6, .distance 1 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 13 2, .gapLower 6 2, .triangle 18 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 45e4a3f9b38502a900c8b483cdc7206ab167d9e8a41d4b21546ee100f3971be2; original global index 5405.
def localCycle00102 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 23 2, .triangle 24 1, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle 470ca6f6231951524ef6baf90826f58414a8ee9b7223f85a0bdbca482f0867a5; original global index 5509.
def localCycle00103 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 487c4b3917b4694ccab405165a07fd0b1b9727f71b8a764a0712fe1d1453fe49; original global index 5618.
def localCycle00104 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 4, .triangle 4 1, .gapUpper 1 4]

-- Original cycle 4a452c792d8a5202ba98b409081574ed1c6adf5f0f483c59f87f121df3136568; original global index 5762.
def localCycle00105 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 2, .gapLower 0 2, .gapLower 0 1, .gapLower 3 2, .triangle 15 1, .corridorLower 2 3]

-- Original cycle 4b5ca96af27c3ec799f74ba3282d6a615d5fd059e292286518a3d78e6e206290; original global index 5838.
def localCycle00106 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 4c58ad5b701d07034b66392851eda0bf2621178c5f9c35218044f3381c36a897; original global index 5926.
def localCycle00107 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 4d3a4725fb4aa614dba302a529ac9a87c654e25be8d644c89ff65b74827df115; original global index 5998.
def localCycle00108 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .triangle 30 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 4d52cd578a5e010759c15da637d158c41f6c640c2c0ef679c14b19b317c485b6; original global index 6005.
def localCycle00109 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 6, .distance 0 5, .distance 0 4, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 2, .gapLower 0 3, .gapLower 0 2, .gapLower 4 2, .triangle 16 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 4fb6edf5c20d2771e5c0fe364d38c83cce9d0976bdae39be84d58a6110455a75; original global index 6190.
def localCycle00110 : Cycle where
  length := 3
  data := {
    node := ![.theta 5, .distance 5 6, .theta 6, .theta 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 0, .gapLower 6 0, .thetaNext 5]

-- Original cycle 517849866cf666a550cba1944f4476912bc0e07458c6fc90df0be0817c204b56; original global index 6336.
def localCycle00111 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 3]
    constant := ![2, 0, -2, 0, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.gapUpper 3 3, .triangle 11 2, .gapLower 0 3, .triangle 12 1, .gapLower 0 1]

-- Original cycle 52744ae2bdec6e46de468c9b674f455eaca06350578308d4b2cea37e3d2c610d; original global index 6411.
def localCycle00112 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 0 5, .distance 2 5, .distance 2 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 3 2, .triangle 7 1, .triangle 30 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 52d28bc571c8ae6f706bc981daaa1a618bb14bc85782b2c66fbfde75738a0790; original global index 6447.
def localCycle00113 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .gapLower 6 2, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 5664a23aaf9a4d58d9063450e07f6ceb7fc4e84ae99b8bf1e27e149f59ec16bd; original global index 6700.
def localCycle00114 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .gapLower 6 2, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 57932b9f0b7102dc1e049d50fd57dda8ca7eb644227ac03a4c6d1551cb499a29; original global index 6799.
def localCycle00115 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 0 1, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 5912bc0521f71e95f82c86232cf6dc54b93198787e60b9cbe9b31c0fb68f49b6; original global index 6908.
def localCycle00116 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 0 1, .triangle 3 0, .triangle 17 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 59b2967264f901cc1d6f865b132f82919ffc7c7efd2df32f9f105a35a54974b5; original global index 6979.
def localCycle00117 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 2 6, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 1, .gapLower 6 1, .triangle 30 1]

-- Original cycle 59e0d6317bdb989a12683a1e7fde4aa0d830fed07c7d643559a4e9dfa3c9fa1a; original global index 6991.
def localCycle00118 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 5a5529c07f2d820c27a4255974c24c7294926c84e3d9f428b19296e0755de634; original global index 7030.
def localCycle00119 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 4]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 3, .gapLower 6 4, .gapLower 6 3, .triangle 13 1]

-- Original cycle 5aa1e9540a10bf591bd1e46743f848a8346cfcefabf2f8ec383cf24abc2c72a6; original global index 7055.
def localCycle00120 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 6, .distance 0 5, .distance 1 5, .distance 2 5, .theta 5]
    constant := ![3, -1, -1, 0, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 14 2, .gapLower 0 3, .gapLower 5 2, .triangle 17 1, .gapLower 5 0]

-- Original cycle 5c3d2dc640149d50db4d354a07707eb9c71c8c54a1064b9432b2e4347b78479d; original global index 7181.
def localCycle00121 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .gapLower 6 3, .gapLower 6 2, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 5ce1dca3d20fe94ea4ff103cc1b22b246ba5c5a68dfd68090d6e18e023833923; original global index 7229.
def localCycle00122 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 5, .gapLower 2 5, .gapLower 0 5]

-- Original cycle 5e576b60c40a8eb32abc42e3ce78edfdac1ea5c81727c156b286cbe7446fd840; original global index 7337.
def localCycle00123 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 4 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 32 1, .gapLower 6 3, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 5e9f1fdf388cdb05dd3fdccd5e2f751b9dada3193d1ee2ced7de7c9163ff850f; original global index 7360.
def localCycle00124 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 3 2, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 6056fcf2c333affaa0866940cc039b11b2fa0816b9143611563f9c0442a8fcee; original global index 7503.
def localCycle00125 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, 0, -2, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 60b7e676265ad7ed04362803a762fc03d09882076d06e432ceb26aa55bb56c07; original global index 7533.
def localCycle00126 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 4 3, .gapLower 0 1]

-- Original cycle 6137c552f79f4b1699ec492df559e7b5cbe132dd288d2c59a8f6c7b3ebfb1b79; original global index 7581.
def localCycle00127 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 9 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 63319c76e21550f46bd1466fa2c35f46c7774b364bd10d6718977295e039b7d2; original global index 7737.
def localCycle00128 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 4, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 0 1, .triangle 2 0, .triangle 16 1, .gapLower 4 0]

-- Original cycle 63f43007886ee20ab85e5e7171a6f75635c12447bc70eeac9f0df516af357207; original global index 7790.
def localCycle00129 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .triangle 3 0, .triangle 2 0, .triangle 16 1, .gapLower 4 0]

-- Original cycle 647579ab3c64cb78f3d62633be07a84f2d0975c205b881fcc094efc4d3d3f3ee; original global index 7823.
def localCycle00130 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 4, .distance 2 4, .theta 4]
    constant := ![3, -1, -2, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .gapLower 6 2, .triangle 4 1, .triangle 2 0, .triangle 16 1, .gapLower 4 0]

-- Original cycle 651a4e7dc6f295a80b166a1ae96588f9265b230fb731c62b9f3d248027edfc82; original global index 7865.
def localCycle00131 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .gapLower 1 4, .triangle 0 0, .triangle 2 0, .triangle 16 1, .gapLower 4 0]

-- Original cycle 658a46790e5db7f354f54850a7b4c7164392681bb4986233c67c2ce5267a26a0; original global index 7900.
def localCycle00132 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, 3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 17 1, .triangle 28 1, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle 659ad0816144278d5cfa7bc0c6991c733cf5630edd4eaf200a6a71e194aba020; original global index 7905.
def localCycle00133 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 2, .triangle 3 2, .triangle 14 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 65c0d18aeb3e7f2228dd720c3df6ec909846f599aed2af680e2472adc0eddb15; original global index 7916.
def localCycle00134 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 2 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 17 1, .triangle 30 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 65e80772d2765d8ad9e52bbc68a73d135ec0137ac6ddecf3888ceb510e8597f1; original global index 7930.
def localCycle00135 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 0 1, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 0 0, .triangle 4 2, .gapLower 0 3, .triangle 12 1, .triangle 9 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 6606d5ee93f7f9e07ebb95f4d6c7e72d93443affab8988b8d50a4430b83d7354; original global index 7939.
def localCycle00136 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 13 0, .gapLower 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 66334695409d613af4da78ce32fc6423f6d482c56bedf964e62953a8b562e8f9; original global index 7948.
def localCycle00137 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 8 2, .gapLower 6 1, .gapUpper 2 4]

-- Original cycle 663f5cbc5b0f2baafa3c38c01ad04131079be0b4710f55154c46f5e31b90597c; original global index 7954.
def localCycle00138 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 2, .distance 2 6, .theta 6, .distance 4 6, .distance 3 4, .distance 0 3, .theta 0]
    constant := ![2, -1, -2, 2, -1, -1, -2]
    coefficient := ![1, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 6, .triangle 8 0, .gapLower 6 0, .gapLower 6 6, .triangle 32 0, .triangle 9 0, .gapLower 0 0]

-- Original cycle 69567951fd66a2817390bc307e3b431a7add8027c77b70fbed782f83eb7c6c10; original global index 8195.
def localCycle00139 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 18 2, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 69abc273861ccbb88641453adf177e689dd8681e2f5b5f080ec5302af601f443; original global index 8225.
def localCycle00140 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 0 0, .triangle 2 0, .triangle 19 1, .triangle 21 0, .triangle 32 1, .triangle 29 0, .gapLower 4 0]

-- Original cycle 6ac5f608d9fc0cdf79c26f000388e780ab1267c811b264feebc7a34446ddd8e0; original global index 8313.
def localCycle00141 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 6, .distance 1 6, .distance 2 6, .theta 2]
    constant := ![4, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 0 0, .triangle 4 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 2 6]

-- Original cycle 6b1204f508b2184310dda10cd0326b4c01191011d66b94a8a13d0a28fcd13ebb; original global index 8334.
def localCycle00142 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 6, .distance 0 5, .distance 1 5, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .gapLower 0 4, .gapLower 0 3, .gapLower 5 2, .triangle 17 1, .triangle 26 1, .corridorLower 2 3]

-- Original cycle 6b21b000daaf2726f1d166c71d7b8e7e84fc1aca854c43cd6cc62485e8010338; original global index 8339.
def localCycle00143 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 0 1, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 6bc6023086be577ff4a8550e6cb91991a87e1c0e2797f768890389b82879e654; original global index 8392.
def localCycle00144 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 22 1, .triangle 23 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 6f0792d727f1554e1da0a80cf7edd66d00efbefa3a2b3c3ad9523d225059090d; original global index 8610.
def localCycle00145 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 2, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 28 1, .gapLower 4 0]

-- Original cycle 6fde949f40f3cd9a073da5015fe1f2dfd5ed630c8cce4d6fa4335018a4775850; original global index 8675.
def localCycle00146 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 2, .triangle 14 0, .triangle 30 0, .gapLower 2 2, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 7038d077fbae03b44db0a9443a3c5d772032e05d5a901121538aa615c792b799; original global index 8691.
def localCycle00147 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 30 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 707f112f57eba890cd38198748ed6af84c1d65a73499539571143c7441448b77; original global index 8716.
def localCycle00148 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 2, .gapLower 0 4, .triangle 3 2, .triangle 12 1, .triangle 9 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 70dd6a4b55fc72bbf943279b1725e3419add7867f5ca1425a0c33f5b52583bc6; original global index 8747.
def localCycle00149 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 0, .triangle 31 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 7104c190dcbab8d4c2284542d13e181b0898be68d0c6cdb81f898c74c245b940; original global index 8768.
def localCycle00150 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 5, .distance 2 5, .theta 5]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 0 0, .triangle 3 0, .triangle 17 1, .gapLower 5 0]

-- Original cycle 7148d404889e89028fcac42542979b74be22738cf3b378232a8d4f236bd37c34; original global index 8786.
def localCycle00151 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 0 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .gapLower 0 3, .triangle 10 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 722295d501633b5132045c21aa8eff9456e6a52f87cbe323e6c23b77c2291839; original global index 8847.
def localCycle00152 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0]
    constant := ![2, -2, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 4 1, .triangle 3 0, .triangle 22 1, .triangle 19 1, .corridorLower 1 3, .thetaNext 0]

-- Original cycle 75081e737a70b932f1cec7de22a6a2a567c8405203897b77c170765e1c17a822; original global index 9070.
def localCycle00153 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 75b2f6f2a919e32246bf206e89c419f469e55f3b8c61c86663c851ebe556ae27; original global index 9122.
def localCycle00154 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .gapLower 5 3, .gapLower 0 2, .triangle 9 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 768c5b2a409c134e678065c94b48979d756094582c92b7eea583ecdb9d254260; original global index 9173.
def localCycle00155 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 14 0, .gapLower 0 2, .triangle 9 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 775a05196b4fcf7142298be4564db32f1698dcb6c8acbbdf88f1a5e86e512428; original global index 9234.
def localCycle00156 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 14 0, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 77edce7d403d683eadc949a4df11e46d37dcf72b855c980b13ff09415ef89019; original global index 9274.
def localCycle00157 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 4, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 14 0, .triangle 3 1, .triangle 2 0, .triangle 16 1, .gapLower 4 0]

-- Original cycle 789bf5ad4b53a11c1d96824364ed984d767323e65c0cdb53e697a6800a72e050; original global index 9330.
def localCycle00158 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 1, .distance 0 5, .distance 0 4, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 2, .gapLower 0 4, .triangle 3 2, .gapLower 0 2, .gapLower 4 2, .triangle 16 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 79525c2668af02d14e81d3a88820d6719363d9b90e44eac8d586f7e11f40f49b; original global index 9387.
def localCycle00159 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 0 0, .triangle 3 0, .triangle 17 1, .triangle 28 1, .gapLower 4 0]

-- Original cycle 79e508c773123c6183466697060bb61d7937b5cdcae4d9acbd0ec43aee1daf53; original global index 9427.
def localCycle00160 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 20 2, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 7af5c14aad43b6d851b77ddd199c7df703b7fd4d5ad3fdcc4f9e10988f29f201; original global index 9520.
def localCycle00161 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -3, 3, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 24 0, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 7b9ed4012c4c5cb9683c2fe1b344f3a5754c8347473cda19c4fcf9a8356a232e; original global index 9565.
def localCycle00162 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 1, .distance 1 4, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 18 0, .triangle 8 0, .triangle 0 1, .triangle 2 0, .triangle 16 1, .gapLower 4 0]

-- Original cycle 7ca7caf9adb3bfbd7aaf42117d15a2172899cd7e0fefd468c23b7602f6591d66; original global index 9652.
def localCycle00163 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 12 0, .triangle 9 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 7d0f8bef71c7765e13162451d109f7c866622a1e890da610ad1b96c7ca9c41fc; original global index 9682.
def localCycle00164 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 2 6, .distance 0 2, .distance 0 1, .distance 1 5, .distance 2 5, .theta 5]
    constant := ![3, -1, -1, 0, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 2, .triangle 18 1, .triangle 8 0, .triangle 0 1, .triangle 3 0, .triangle 17 1, .gapLower 5 0]

-- Original cycle 7d5f9b57e64d728a49530a8363855abd638e30701a181d1d6f9c007647600185; original global index 9718.
def localCycle00165 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 4 2, .gapLower 6 2, .gapUpper 1 4]

-- Original cycle 7dda1de1afb255a0442fa57307e2509c02ed69a0f154961e145eb2eb21ee1d35; original global index 9773.
def localCycle00166 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 2 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 17 1, .triangle 30 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle 7ebc867532c3bb220a0e0a32d9954ee041a442cacbe5079d08baeacc9a5093c8; original global index 9841.
def localCycle00167 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 2 5, .theta 5]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 2, .triangle 4 0, .triangle 3 0, .triangle 17 1, .gapLower 5 0]

-- Original cycle 7fb775c1dfc16d7488f04a6c43214ca8741997285945cd99dd8f7ee4609c8bf6; original global index 9904.
def localCycle00168 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 13 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 81f2ef460e17e94bd6c510b7f522a5a127680d815d1146f91e8af48b8e0c0157; original global index 10089.
def localCycle00169 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 3]
    constant := ![4, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 0 0, .triangle 2 0, .triangle 19 1, .triangle 21 0, .triangle 27 0, .gapLower 3 0]

-- Original cycle 83f9d2d65a308cef503f222c9be63f87e9ac37db8c365bfd821ff3fad5b9e132; original global index 10244.
def localCycle00170 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 0 6, .distance 0 5, .distance 0 4]
    constant := ![2, 0, 0, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, true, false] }
  origin := ![.gapUpper 4 3, .triangle 13 2, .triangle 14 1, .gapLower 0 2]

-- Original cycle 8442643f6df2061ede284134f230a84acc16e9762d3c3224a1fd6690fb5dac31; original global index 10270.
def localCycle00171 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![2, 0, -1, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 5 4, .triangle 12 0, .gapLower 0 1]

-- Original cycle 849a689c6036daf36aae27352d473715181ea843143ac7082613ccf695a44aa8; original global index 10297.
def localCycle00172 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, 0, -2, 0, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 21 2, .gapLower 6 2, .triangle 14 1, .triangle 3 1, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 85f269d89d32152107553103a2530586fa14257b1514bd70f16f694c3a870e2f; original global index 10392.
def localCycle00173 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 0 5]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 5 3, .gapLower 6 3, .gapLower 6 2, .triangle 14 1]

-- Original cycle 8714854638e23393e829af3eeb4e49e6be648f87b49636c5b5920069439c6e8f; original global index 10480.
def localCycle00174 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4]

-- Original cycle 874b666758e05425d0cb1f61f6facf408808d3e0188fe67578f8981864c6e15d; original global index 10492.
def localCycle00175 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 0 0, .gapLower 0 3, .triangle 12 1, .triangle 9 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 88d7ad6dc479fe1c4aa0615bf4758274e3e2d9529ff28d127e92926617bd5a70; original global index 10600.
def localCycle00176 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 1, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 0 1, .gapLower 0 3, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 89719e19e5af164188cc7c144562f16a8b39d6080203aacc0a0976d80f3c4673; original global index 10636.
def localCycle00177 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle 8979fa159680c6a4993032c675d6716adc13764c4930785e2be5e6346c235378; original global index 10642.
def localCycle00178 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 13 0, .triangle 9 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 8998d3014fb2c97aaddbb3ef483dac35612958050704a156c17d806e14c53184; original global index 10656.
def localCycle00179 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 4, .gapLower 2 4, .gapLower 0 4]

-- Original cycle 8a60e87246bb0de4d7ff9e9321ff37fbb96b4bf44511b9499d42ca5aff1a6141; original global index 10724.
def localCycle00180 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 4]
    constant := ![2, -3, 0, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.gapUpper 4 3, .gapLower 6 4, .triangle 4 2, .triangle 13 1]

-- Original cycle 8b3d7e26bb0591d10e16447f6d9a54c5597eca9b205cf30b36c7aacfc3c13f35; original global index 10788.
def localCycle00181 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 3 4]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 3 4, .gapUpper 5 5, .gapLower 6 5, .triangle 32 0]

-- Original cycle 8c59d67da26b1ccae5cbcfd28337201af97adfef72da747fd334428543058bac; original global index 10860.
def localCycle00182 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .triangle 29 1, .gapLower 4 0]

-- Original cycle 8dade44d86d6defbc3126304c825784f75b1ac1bfb3f6a3980e59721a29b712e; original global index 10959.
def localCycle00183 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, 0, -2, -2, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 28 1, .gapLower 4 0]

-- Original cycle 8dba7770323103c6b60d2dbc4d3a392797a7942a8f52b142aac5b5ea608db62b; original global index 10965.
def localCycle00184 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 3 6, .distance 4 6, .distance 3 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 32 2, .gapLower 6 4, .gapUpper 4 5]

-- Original cycle 9081a9bd11a831c9a76fc241e80cd14c85b605212c42dc8fcaa24168cd871347; original global index 11184.
def localCycle00185 : Cycle where
  length := 4
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .theta 6]
    constant := ![3, -2, 0, -2]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 27 2, .gapLower 6 0]

-- Original cycle 912bce598e8287c27671c875a8d9af363ec54770052bd1b3e43b345f3a2010c3; original global index 11242.
def localCycle00186 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 5 3, .triangle 14 2, .gapLower 0 3]

-- Original cycle 91f8b25136d396d518d37a6efefb505a5a319b4d2f73a9df5429d0b6bd74c376; original global index 11313.
def localCycle00187 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 3 2, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 928a672a66a4cea977a2fcd38fe221d5bed65e70253946dc5053b7a98debb241; original global index 11353.
def localCycle00188 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 938619127337ee74ad09042fb8a396268d77694b64ace1698095968b073524bd; original global index 11444.
def localCycle00189 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 3 6, .distance 5 6, .distance 3 5]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 33 2, .gapLower 6 4, .gapUpper 5 4]

-- Original cycle 93da994b94ed79e9cdb7f15535e4aa5969c21605448a673f3a90ebb4d5ec3701; original global index 11472.
def localCycle00190 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 30 2, .triangle 18 0, .triangle 0 0, .triangle 3 0, .triangle 17 1, .triangle 28 1, .gapLower 4 0]

-- Original cycle 95137ceb4629741422f4628544afcfb321f17b20adacaec8151bc368fe2be8ab; original global index 11581.
def localCycle00191 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 9 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 953e8c21043e6a5d896c9dabb8399b4b7eeb46af07fa031725fa48c84fe02edb; original global index 11594.
def localCycle00192 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 2, .gapLower 6 2, .triangle 8 1, .gapLower 6 0]

-- Original cycle 9683dce14b0f798286fcfd1ddee0b61d324c8ad8e6026f197f933b6819729802; original global index 11705.
def localCycle00193 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 5, .distance 2 5, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 2, .gapLower 6 2, .triangle 4 1, .triangle 3 0, .triangle 17 1, .gapLower 5 0]

-- Original cycle 96b9494473ce03ea732d28652e07e9cdb6bb9784746a6ec4403ce1778e64bb99; original global index 11720.
def localCycle00194 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 96e99b0abf5bee781d358e490e4450e72a70b21d5ef73566b1583d160a72e9f6; original global index 11729.
def localCycle00195 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.gapUpper 5 3, .gapLower 6 3, .triangle 4 2, .triangle 14 1]

-- Original cycle 9724406ec004ede95f84d06f0b2ec135619be5c5b3c36fa742ad94e0d73493d5; original global index 11746.
def localCycle00196 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 0 1, .distance 0 6, .distance 0 5, .distance 0 4, .distance 1 4, .theta 1]
    constant := ![4, -1, 0, 0, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 0 0, .triangle 4 2, .triangle 14 1, .gapLower 0 2, .triangle 2 1, .corridorLower 1 4]

-- Original cycle 98913307323545c95c33dbb530c4d687ffd4be9f07d2787fc5f2c74d84a6d56c; original global index 11850.
def localCycle00197 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .triangle 8 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 995b7e295eabd55355eeeabfcee763e73b75706d5c4b2499dfbae6687ac3be35; original global index 11907.
def localCycle00198 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 14 0, .triangle 3 1, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 9c80c84c3c3326c3acc40e823977da357e8540e1b5c36ccf84afeca27079a132; original global index 12172.
def localCycle00199 : Cycle where
  length := 5
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 2 6]

-- Original cycle 9c97f6e443be0ba44fbf4a45707e427364ab05396e8544bb1c6786bf28d11b85; original global index 12180.
def localCycle00200 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 0, .triangle 3 0, .triangle 2 0, .triangle 19 1, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 9ca3d13f81233237acb5698cf037899af969d83ad820200461c2b07a651219c3; original global index 12186.
def localCycle00201 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0]
    constant := ![1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true] }
  origin := ![.gapLower 0 6, .triangle 0 1, .triangle 4 0, .triangle 24 1, .triangle 22 1, .triangle 19 1, .corridorLower 1 3, .thetaNext 0]

-- Original cycle 9d13c68342d2c67d4df7a5e4fade4e9c08277ebda0ab8b119df4fdbe27ae206d; original global index 12216.
def localCycle00202 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -3, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 9e313005d3a5d5cb42ff493703425a422ea2dc9f311372737352bbef21edd585; original global index 12313.
def localCycle00203 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0]
    constant := ![1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.gapLower 0 6, .triangle 0 1, .triangle 3 0, .triangle 22 1, .triangle 19 1, .corridorLower 1 3, .thetaNext 0]

-- Original cycle 9e6b5af7ccac8c734d84d5bf1754b9f5eb9c12900e1bdc494c18053606e76661; original global index 12337.
def localCycle00204 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -2, 2, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .gapLower 6 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 9e933a11dad1973ff8f9428e0e87591336b91cdac46a5b95e0bf0d9f7bf7c66b; original global index 12350.
def localCycle00205 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 19 1, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle 9f4f7d2c515c0885a40b8f918b771eb17822af58d57d44d4e6d19d77bed5dd59; original global index 12401.
def localCycle00206 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .gapLower 0 2, .triangle 9 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle a11925529057de4bd493e0e186591dbf17d6b9a915b81eef3d18c8b0aadcb184; original global index 12529.
def localCycle00207 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 0 6, .distance 1 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .triangle 4 1, .triangle 18 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle a34d76e2ca943dace0823a72eb535d6990e6b621065ca4541078cfa6f7d03992; original global index 12691.
def localCycle00208 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 4 6, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 23 2, .triangle 24 1, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle a44a301a52cc9397fd63ca6320358d871a1696bf3e39b9dc1614ef704bb050da; original global index 12769.
def localCycle00209 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 4, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .triangle 4 1, .triangle 2 0, .triangle 16 1, .gapLower 4 0]

-- Original cycle a55e17a76fe63d74a4b4db3978d653b659cc08cf7cee86c2bb1741eb3bb607c7; original global index 12845.
def localCycle00210 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 33 1, .gapLower 6 3, .corridorLower 0 6, .thetaLower 0]

-- Original cycle a5aa4432b9008feacf0654347bdfdaf229916aa0ca3fce4e3b5656c8ef1e7874; original global index 12870.
def localCycle00211 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, 0, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, true, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 0 1, .triangle 4 0, .triangle 18 1, .triangle 30 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle a5eb29f3412acd98554156d161bb06157173d273720445954d6e3d68dc228a94; original global index 12891.
def localCycle00212 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -3, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 18 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle a6f90f1cc7d9babaa37fa603ccff7919824d7760fe27684c0fcf025e61fc8058; original global index 12975.
def localCycle00213 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 1, .distance 0 5, .distance 1 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -2, 0, -2, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .triangle 4 1, .gapLower 0 3, .gapLower 5 2, .triangle 17 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle a6f98f71efb24971d37dda8c69bfbad9885ce525de60b37cc1baa5a201040eaa; original global index 12977.
def localCycle00214 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 13 0, .triangle 9 1]

-- Original cycle a7efc570ed68346d0c4eeede7ada625ca8ac9ec1991622105401a7c1c47f3597; original global index 13073.
def localCycle00215 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 0 1, .triangle 2 0, .triangle 19 1, .corridorLower 1 3, .thetaNext 0, .thetaLower 0]

-- Original cycle a92fa543a2cab5245df79b3b728874a006164725b827edc997cb5ba0af1e15f8; original global index 13171.
def localCycle00216 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 4 3, .gapLower 0 1]

-- Original cycle a9707215f99a8e69d5fcd6ef958d61def534f35a301e1e20c240afc21aadd29c; original global index 13190.
def localCycle00217 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 3 6, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 33 1]

-- Original cycle aa36aa17a9f732f854e2002e05fc0927a8b4bf5dc330c2b39de03f9d4368ae22; original global index 13251.
def localCycle00218 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 4 2, .gapLower 6 2, .gapUpper 1 4]

-- Original cycle aab84606924dc2022c3335c8c1e3188a85628142972293e3c0fac1ecc4ac73d8; original global index 13302.
def localCycle00219 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 21 2, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle aaf9da7484eb8372a12eff2398d552bbf04e9f037e34bf49ebaded5d22528e68; original global index 13317.
def localCycle00220 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle abf02bf45f656f49b6ac1f14af01181ca002e9ddb4d18fa30e490705afcb7509; original global index 13392.
def localCycle00221 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 3 6, .distance 4 6, .distance 3 4]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 32 2, .gapLower 6 4, .gapUpper 4 5]

-- Original cycle abf8cde7fe43d406d63161e4f61b3498fc623df5fedbd551eb3f8592ec152cbc; original global index 13397.
def localCycle00222 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle ad59efc32f0c6f00f009b5138f2816ac35f48ca6f2800bacab9bcafdf3162fa7; original global index 13518.
def localCycle00223 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -2, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 2, .gapLower 6 2, .triangle 4 1, .triangle 3 0, .triangle 17 1, .triangle 28 1, .gapLower 4 0]

-- Original cycle ae90eba61d4dac8c176504a78f4840f7e8fbd3f2be6039bf2d2c4d1d72e872c9; original global index 13626.
def localCycle00224 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle aef4ee32c9c67db96f09a7934f1243825e72c9eada4d5d930c5a229b91a71da7; original global index 13658.
def localCycle00225 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 3, .triangle 17 0, .triangle 0 0, .triangle 2 0, .triangle 16 1, .gapLower 4 0]

-- Original cycle af431c4ec88953e47cad4cda3b4e3d8dc4f7bbdc463297be6fbdcff7a5011457; original global index 13692.
def localCycle00226 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 3 5, .distance 0 3, .theta 0]
    constant := ![2, -1, -2, 2, -1, -1, -2]
    coefficient := ![1, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 6, .triangle 8 0, .gapLower 6 0, .gapLower 6 6, .triangle 33 0, .triangle 10 0, .gapLower 0 0]

-- Original cycle afbb3a719837fd464f97e2fd4646b35de4e7d4dc39821577fa628bd95eab7628; original global index 13726.
def localCycle00227 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 0 1, .triangle 3 2, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle b1c7e201957598b885e987024f63b14ace64fd0711851301d9a6927fbd7a550e; original global index 13893.
def localCycle00228 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 4 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 29 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle b2036a1b56c820e4dfb3f666acd72d2735d642cf961d01d1df48a317bd00c414; original global index 13909.
def localCycle00229 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .gapLower 6 3, .triangle 4 1, .triangle 18 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle b27b0780470737c56afc17a9f93ad6f3a23a25bce3b49438fc15078fcaf33e39; original global index 13945.
def localCycle00230 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![0, 0, 2, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false, false] }
  origin := ![.triangle 2 2, .triangle 9 1, .gapUpper 3 3, .gapLower 5 4, .triangle 28 2, .triangle 17 0, .triangle 0 0]

-- Original cycle b2c6e8ed284428168849d85eeb5cf5de725317fac5917832e436063287feaacc; original global index 13974.
def localCycle00231 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 6, .distance 0 4, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, -1, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .gapLower 0 4, .triangle 13 1, .gapLower 0 1, .gapLower 3 2, .triangle 15 1, .corridorLower 2 3]

-- Original cycle b31e754409141f568e22944672c49c754910f9660ec6842870baf39c44f78dd0; original global index 13997.
def localCycle00232 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .gapLower 6 1, .corridorLower 2 6, .thetaLower 2]

-- Original cycle b331293ec68091434cbade7f18ee013c4c3173b68a616789c1256fefd6d9a8a1; original global index 14003.
def localCycle00233 : Cycle where
  length := 5
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .triangle 8 1, .gapLower 6 0]

-- Original cycle b39d49e70d68594ffe22d17ab88b4a34430effc4c7624976dfe1340d077a1c95; original global index 14031.
def localCycle00234 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 30 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle b4d9ac179e5c66e769dda42b7b6ec26dd394421f0e270f89ddd0dd857dfe5174; original global index 14124.
def localCycle00235 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 2 6, .distance 5 6, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 30 2, .gapLower 6 1, .gapUpper 5 1]

-- Original cycle b5741e09a0054781962f2967196032706fb002571bbb072506693bbc0b160a11; original global index 14177.
def localCycle00236 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle b62e28e80f495baafe3ace4c9823f4dd53685ffd1830b392aecde7c0744f890f; original global index 14230.
def localCycle00237 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle b669f99f18700681adc13b3465108b06bc81180ea8d40e4b3abccb8440ce3fa0; original global index 14256.
def localCycle00238 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 7 2, .triangle 14 0, .gapLower 6 1, .gapUpper 2 4]

-- Original cycle b7ce7cefc543e3485473eda45cce18c69355a9fb60418ddbfc5e902f6b535ff2; original global index 14343.
def localCycle00239 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 17 1, .triangle 28 1, .triangle 29 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Original cycle b8a16dc489c1ed096f48f63ffece10de0226f2516d7c8286a549c89e03523ac5; original global index 14407.
def localCycle00240 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 2 5, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 33 1, .gapLower 6 3, .triangle 4 0, .triangle 3 0, .triangle 17 1, .gapLower 5 0]

-- Original cycle b97704d29d976b32d9fa474dd266c172091d546830e95bc765c031c06af89239; original global index 14471.
def localCycle00241 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .gapLower 5 3, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b9e9f5cc39fb62169bb42c57c57d6f776afe4de6f82c2f4fcd0263a2f296db78; original global index 14516.
def localCycle00242 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 4 2, .triangle 8 1, .gapLower 6 0]

-- Original cycle bab9af5ace4d50e17ae88639e1c51ecd205d0e3684478018f4784a00eddb55ce; original global index 14584.
def localCycle00243 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle bb27136a9ba20ea64cd5694d66f399f0321c023e711f9e35cf7e81595b3df1f0; original global index 14612.
def localCycle00244 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 0 1, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 0 0, .triangle 4 2, .triangle 14 1, .gapLower 0 2, .triangle 9 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle bb2856fe7031e381cfd1573854d8a00be086c47a4c4645dd948ce3df86d9bb6e; original global index 14614.
def localCycle00245 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 23 2, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle bd3c86fe6956f6787c8c995185f90589dddc8247121febe283def7a897be5100; original global index 14760.
def localCycle00246 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 12 0, .triangle 9 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle bd9b40e6eb92b4fd7525a2c671417cb4a83f546ff633dab3797266b173c52a76; original global index 14789.
def localCycle00247 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .gapLower 4 0]

-- Original cycle bdb13c79662b40577a662ad287fe553cb3550a1229ef32f7ff2fe1674fc214eb; original global index 14797.
def localCycle00248 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 2, .gapLower 6 2, .triangle 8 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle be0ef70b612db758d2ac0e1c8ef429b9e8261dc3d71a1dc54bd54f42f6246ac6; original global index 14821.
def localCycle00249 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -2, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 28 1, .gapLower 4 0]

-- Original cycle be78506cc3f8da68a57de8cf2370282d5b96424c6e4615969f600be6fabd69b8; original global index 14861.
def localCycle00250 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 21 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle c0140fe255e0a7c22844f13bcd18b1965389af21c8ab242a257ab90dfdcaa34b; original global index 14993.
def localCycle00251 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 32 2, .gapUpper 3 6, .thetaLower 3]

-- Original cycle c1212de25f6c2182104a14e4d48a8f66c414e2b1a9101994636db9764adb2952; original global index 15074.
def localCycle00252 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .theta 4]
    constant := ![3, -1, -3, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .triangle 4 0, .gapLower 1 2, .gapLower 4 1, .gapLower 4 0]

-- Original cycle c201703793907d803056c39ebb86cb776cfb1bb89e1985cdb25d65710ca38f64; original global index 15149.
def localCycle00253 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 22 2, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle c265987c688df4b000eb71382661b89c0e2cb1b49bd8e9b9fc952bf7966b3f93; original global index 15178.
def localCycle00254 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle c2d4ee542138ecf62aa3fea2e81067c224ec3576913bc4f1eb0c210ddd10a8a9; original global index 15204.
def localCycle00255 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .theta 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -2, 2, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 18 1, .gapLower 6 0, .gapLower 6 6, .triangle 34 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle c647b1ac5493d2f4d51524214cb208d0cad45c5f7b3187486db367449c76908f; original global index 15463.
def localCycle00256 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 3 2, .gapLower 0 2, .triangle 9 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle c6b3db934ba66585fb31b19d7b944624b5c614841f8c7186e30b2a6033455e62; original global index 15502.
def localCycle00257 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 0 1, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 0 0, .gapLower 0 4, .triangle 14 1, .triangle 12 1, .triangle 9 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle c6bb36e8ea0e93db08e165730d04b9691788949061f35690e470f4ea6c02df06; original global index 15507.
def localCycle00258 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -3, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .triangle 4 1, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle c700c61897ff62d29eca21d8bf5ba8719dbdaa133c71e3c6fe50f3ac3d00e214; original global index 15530.
def localCycle00259 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -2, 2, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .gapLower 6 6, .triangle 34 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle c721fb6ec6b63561144fdc24a9f754b56e75f013cf08b903a62098b6b6d40802; original global index 15538.
def localCycle00260 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 21 2, .triangle 24 1, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c7293b9cd3feed625d7368b5de58113b8d503072ac7ed5a56ed61c9139176ec4; original global index 15541.
def localCycle00261 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 5, .distance 2 5, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .gapLower 6 2, .triangle 4 1, .triangle 3 0, .triangle 17 1, .gapLower 5 0]

-- Original cycle c835f95a8e08dada703d3ae20cb091607def5b3e5731755966ff456a26576152; original global index 15625.
def localCycle00262 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 0 1, .distance 1 4, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 30 2, .triangle 8 0, .triangle 0 1, .triangle 2 0, .triangle 16 1, .gapLower 4 0]

-- Original cycle c88dc8d8a33d04e4a75683179a25f6ab6d0c3669c1dca44a7f1c953ea64653d6; original global index 15663.
def localCycle00263 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 9 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle c8b9d869a77a4942e675c8bbb14e668b883dc57a685a009ca598bfac44319733; original global index 15679.
def localCycle00264 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 24 2, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c9f7c6d368a18bae288181bdbb45b3962377c04ed5d34b45625736d45cb8545d; original global index 15784.
def localCycle00265 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -3, 3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle caf1b77b7a299a3f3dbde4a958be7513686a2dbe852427f471faed2ec91dfa99; original global index 15857.
def localCycle00266 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle cb863e61b69a15785236e88ac84da36878dd5b32b0b26ca0ffa75e58e582b05e; original global index 15904.
def localCycle00267 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 4, .distance 2 4, .theta 4]
    constant := ![3, 0, -2, 0, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 23 2, .gapLower 6 2, .triangle 4 1, .triangle 2 0, .triangle 16 1, .gapLower 4 0]

-- Original cycle cbbed3091b552467b06aa446c54f6c376d3f5edb8f92ce9b2f9860a281b7e32d; original global index 15919.
def localCycle00268 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 1, .distance 0 5, .distance 1 5, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 2, .gapLower 0 4, .gapLower 0 3, .gapLower 5 2, .triangle 17 1, .triangle 26 1, .corridorLower 2 3]

-- Original cycle cc449a7de14367159751cd9769b5d2dca6aaf9eb33bf895db2a232430ebd2c67; original global index 15965.
def localCycle00269 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 1 2, .distance 0 1, .distance 0 6, .distance 0 5, .distance 1 5, .theta 1]
    constant := ![4, -1, 0, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 0 0, .triangle 4 2, .gapLower 0 3, .triangle 3 1, .corridorLower 1 5]

-- Original cycle cdf076396319d2de6038402d64a8080efa3f201561a9cf945120c146c9c600eb; original global index 16087.
def localCycle00270 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .gapLower 6 2, .corridorLower 1 6, .thetaLower 1]

-- Original cycle cf82ce4dde7e81bc39228923e8a75cd5d01987095a99e66031d62fff1b804ab0; original global index 16190.
def localCycle00271 : Cycle where
  length := 4
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 1, .distance 0 6, .theta 0]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 0 1, .gapLower 0 4, .corridorLower 0 6]

-- Original cycle cfb8e2544ec97e0ea43942dc5b696a695f44cd3a6e3cb7e4954e763be5d23a97; original global index 16211.
def localCycle00272 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 3 6, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 5, .gapLower 6 4, .triangle 32 1]

-- Original cycle d01c5d09c03d0347f6dcedb2d82a760d2e2e64c27803481c44804e32dccbb722; original global index 16244.
def localCycle00273 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .triangle 4 2, .triangle 8 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d1cee49f152dd265dd4d16760f88a4924dbedd38766ef42413e0404565ed2abe; original global index 16372.
def localCycle00274 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 3, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle d20a6888e65b1176866b568a6758850a20769b1b57fe7aa7b63b1ee760939d56; original global index 16393.
def localCycle00275 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 30 1, .triangle 7 0, .triangle 0 1, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle d2b33a3756d80dd8555269a1912af40b9a2f387597650a0e036148956087012d; original global index 16443.
def localCycle00276 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 0 3, .gapUpper 5 3, .triangle 24 2, .triangle 4 0]

-- Original cycle d2d85fe266b075bf92ba2b25193f43f9467a43b40ff865b2187ce29bd404fc8a; original global index 16450.
def localCycle00277 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 5, .distance 2 5, .theta 5]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 3 0, .triangle 17 1, .gapLower 5 0]

-- Original cycle d3d6263596cc69b3cc562733855838ef906e2cee6f4f4c73a60b2e73c9ce5c77; original global index 16532.
def localCycle00278 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 22 2, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle d3db0719d1766584a6f5e151295942b44c5a0a563d70f20a593b60fb58079d20; original global index 16536.
def localCycle00279 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 4 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 0 6, .thetaLower 0]

-- Original cycle d44f45b95e07e230dae7ef13769cb9cc656c180413e60acf14853129f3bdf3be; original global index 16567.
def localCycle00280 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 1, .distance 0 6, .distance 0 5, .distance 0 4, .theta 0]
    constant := ![2, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 0 1, .triangle 4 2, .triangle 14 1, .gapLower 0 2, .corridorLower 0 4]

-- Original cycle d4752a36aa5edcfceb54199464b54360fa625dff82215cfd3d0e403c0f7bc520; original global index 16577.
def localCycle00281 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, -2, -1, 0, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .triangle 4 0, .gapLower 1 3, .gapLower 5 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle d55109bd4139c4c8722fb32030be1fac348c6ac54b7f988a317b36706014918a; original global index 16647.
def localCycle00282 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -1, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .corridorLower 0 6, .thetaLower 0]

-- Original cycle d55c3b73f0d02875d73158f42a71c4c937e4ab93a9258da14a07ccdb20c47eda; original global index 16650.
def localCycle00283 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 10 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle d680f5b602f13c642eb895d78884608a7858cd76d715de1c1bc5dc3ebd399cbc; original global index 16744.
def localCycle00284 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 3]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 5 4, .gapLower 5 3, .gapLower 0 2, .gapLower 0 1]

-- Original cycle d78aa84bcfa72f513f1f161695a01f92e94e15ab3a4f8a8e6136a4c9de6ff9bc; original global index 16820.
def localCycle00285 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle d8580fecf0f535dfc3559215ca3612356279115384712970a812a05a9d090a51; original global index 16888.
def localCycle00286 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero]
    constant := ![0, 1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 21 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .corridorLower 1 3, .thetaNext 0, .thetaLower 0]

-- Original cycle d8dedbabea0b2c6e84c36d9c2ca66a244a29316014d75c793aff4257574a2af1; original global index 16928.
def localCycle00287 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 5 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 14 2, .gapLower 6 2, .corridorLower 1 6, .thetaLower 1]

-- Original cycle d9578c564e20c307c28622b05311e2c1aa1299a438ab6038bab0fb29241e9d0c; original global index 16986.
def localCycle00288 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle d99af7ea34bcfdb0d37254487fba67c3fb57b9f8ae9f06c8a9016e3556fb3331; original global index 17001.
def localCycle00289 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 5, .distance 2 5, .theta 5]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 2, .triangle 18 0, .triangle 0 0, .triangle 3 0, .triangle 17 1, .gapLower 5 0]

-- Original cycle da0e813525725edd4e8ee3451f7494a5dd4e8128ecd3f2f9ff5452489c6d8862; original global index 17041.
def localCycle00290 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .theta 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -2, 2, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 18 1, .gapLower 6 0, .gapLower 6 6, .triangle 32 0, .triangle 19 0, .triangle 15 1, .corridorLower 2 3]

-- Original cycle db8a91359aa8a701cdb2cd368a87d4db2f946f5f1034d569959019db23c80a1e; original global index 17160.
def localCycle00291 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 4 6, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -2, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 23 2, .triangle 24 1, .triangle 3 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle dc64b284b6047fd6511fd918076087de4ef40eea0309e6d7dbce0097c2ee2247; original global index 17223.
def localCycle00292 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle dcd6be629f851c60f3dda9ddb8c55581d334282bb6f75a6bae998e1d67541926; original global index 17258.
def localCycle00293 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle dd59d9315f781032cd0b906eb690c20487515fdf9b6f3ede7dd974809479791e; original global index 17304.
def localCycle00294 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 22 1, .triangle 19 1, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle ddfb3a2ae0279e104c7a189a8e92e38638a67e8f7ccf1c1cdae214ef1ceb310d; original global index 17354.
def localCycle00295 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 23 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle df0aea2ddd88493b530f2b9293cbe39f42944ef336a5dcaa7b623f87b770c56f; original global index 17434.
def localCycle00296 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .triangle 8 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle dfe29c603dae67e669cd9a7132d7975dddb8147e4f221d4f5f103d697199ceaa; original global index 17496.
def localCycle00297 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 23 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle e0ae65ae1a807027f3215599e1be31b3a967b662b69be1911bc3031043ce6e23; original global index 17569.
def localCycle00298 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 5 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 14 2, .triangle 8 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle e12de6ca108f24754e4d684cd16a7d52461f767f0dad14d677865510975f3601; original global index 17610.
def localCycle00299 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 1]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 1 4, .gapLower 6 2, .triangle 4 1]

-- Original cycle e285606dce36a0a5a924ab0bb413818a26df3c5b6ff622d500ffbb2e736b9abb; original global index 17713.
def localCycle00300 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .gapLower 3 4, .triangle 9 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle e2f0c705c609eb2328bca722074275b9bdb45bcd93e5b55001afc6f44db43441; original global index 17750.
def localCycle00301 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 2, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .gapUpper 3 6, .thetaLower 3]

-- Original cycle e52a9cc34ad6d5d70c3a3050a7c95afe0253d802238b41090bc8b931bba59724; original global index 17913.
def localCycle00302 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -3, 0, -1, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, true, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 0 1, .triangle 3 0, .triangle 17 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle e5c74f634d73578553f445b6300f25676daf479e03771e57c6c1c68c8a678d8f; original global index 17978.
def localCycle00303 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .triangle 14 1, .triangle 30 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle e79cbbcd6d11e1f0f79b5c96e7b7d2aa5bf67c1af1d7b6bff0f62cfeb556e704; original global index 18115.
def localCycle00304 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 6, .distance 0 1, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 14 2, .gapLower 0 4, .triangle 3 2, .triangle 12 1, .triangle 9 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle e859c6d1ab01232e9f718bde7efe65bcf01b8803891fe5da4154a17905e95254; original global index 18163.
def localCycle00305 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 14 0, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle e8d41871eeefafdb72cf268e4349c87585cbaf4be5c1f76e7fd832d176ff769d; original global index 18196.
def localCycle00306 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 0 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 0 0, .triangle 2 2, .triangle 9 1, .triangle 11 0, .triangle 32 1, .triangle 29 0, .gapLower 4 0]

-- Original cycle e8ffd1297463927cd481154d37f2f354d628053aad2df2e3d65939e7debc3f30; original global index 18209.
def localCycle00307 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .triangle 4 2, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle e9392235308234854f294a722c5e1ee2ca79a34205d3fd1d1bbdf975c78bf749; original global index 18224.
def localCycle00308 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 0 6, .distance 0 5, .distance 0 4]
    constant := ![2, 0, -2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 4 3, .triangle 13 2, .gapLower 0 3, .gapLower 0 2]

-- Original cycle ea0781fb605d308182422247566cac8de690a4db14c079bc9e18838501ace7a8; original global index 18282.
def localCycle00309 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -3, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle ea1e13a94dfcba73ab6fc5c0f62b471020bb36ea073a7ced1d0146c748fcf528; original global index 18288.
def localCycle00310 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -2, -2, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .gapLower 0 4, .triangle 3 0, .triangle 17 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle ebd7717191bd72e874a07598e3677b7f87dc874578216fc43e151e0d266b5491; original global index 18402.
def localCycle00311 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ebdd6ea3a227e0246b39e9514756a4c9c0b87e99567638dc25ecc782f3525f9d; original global index 18406.
def localCycle00312 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, -2, -1, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .triangle 4 0, .gapLower 1 2, .gapLower 4 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle ec0094e4e5ed19278e299bb6aa3ff42131d5f26d16fac1293678cf92126a8de0; original global index 18422.
def localCycle00313 : Cycle where
  length := 13
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle ec86ee16b10d3a411f85a58125f0bf457206be913c2e0bbbdf12016c0a6b6c73; original global index 18465.
def localCycle00314 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 11 0, .triangle 32 1, .triangle 29 0, .gapLower 4 0]

-- Original cycle ed1aa9a47937ced5dd404ef0dbffffdca277f7a5521658a530c618d43f8556ef; original global index 18510.
def localCycle00315 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, 0, -2, 0, -2, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 23 2, .gapLower 6 2, .triangle 4 1, .triangle 3 0, .triangle 17 1, .triangle 28 1, .gapLower 4 0]

-- Original cycle ee302d3aaa7eee609a82e79ffef04345bec0c15ddf2b45970e5b952d60b85a60; original global index 18590.
def localCycle00316 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 2 6, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.triangle 4 0, .triangle 18 1, .gapUpper 2 4, .gapLower 0 5]

-- Original cycle ee4bed3390fae9ea600c14c36613854832ff0b2633ac942d61997e33c9e9256f; original global index 18598.
def localCycle00317 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 21 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle ef60358f5812080db1c285acc1d6773d5feae30b57cb2e27685d696397065f1c; original global index 18676.
def localCycle00318 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle ef7fa173d0ea73d5ba7d73b49558d036a97e840a1b5abbdd61f2771542381a7f; original global index 18685.
def localCycle00319 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 3 2, .gapUpper 5 3, .gapLower 6 3, .triangle 4 0]

-- Original cycle f0c1949588c72ceb22408a2ab331e7ef1942151cb446edea11d268dcc6d0ff8a; original global index 18778.
def localCycle00320 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .gapLower 6 2, .triangle 29 1, .gapLower 4 0]

-- Original cycle f1d717ea282173538a507ddb73dc1c7f94404d2df31a3b9e36de6f6547781e63; original global index 18857.
def localCycle00321 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 13 0, .triangle 9 1]

-- Original cycle f24a7cbbfa0078b6d9f4cf883d04ae0d26a3bda8a6bcdc0cb7c4f50b9c506138; original global index 18894.
def localCycle00322 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .corridorLower 5 6]

-- Original cycle f24eba4adfa0adcfdaa6485460eee620798adb561a0fb7511456550628c98a5f; original global index 18896.
def localCycle00323 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 32 2, .gapLower 6 3, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle f2e7ed9177af79973c5620b103a9b1c122046e3039bc72f22610321efa314cae; original global index 18934.
def localCycle00324 : Cycle where
  length := 5
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .theta 2]
    constant := ![3, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .gapLower 6 1, .corridorLower 2 6]

-- Original cycle f4657372bfeadf64919563758a6ab14f2a4c4e542ab96fd8a1f1f3cdd4e0db9c; original global index 19052.
def localCycle00325 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, 0, -1, -2, 3, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, -1, 0]
    strict := ![false, true, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .corridorUpper 5 6, .gapLower 6 5, .triangle 32 2, .gapUpper 3 6, .thetaNext 2]

-- Original cycle f56ff0dd0c79f2a0cf4b7f1094f81dd17d9bd9edbcb242892041e090054a6860; original global index 19135.
def localCycle00326 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, true, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 17 1, .triangle 28 1, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle f5a8f3cdc12f5c59a9a11a9b4e2e2ad0c25d5ec5f299831e1482d8f9c7d490a4; original global index 19158.
def localCycle00327 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .gapLower 3 4, .triangle 9 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle f5d7a028227289192e0e1740e9c95097ea9cc0a44204093b639c2d241d28b8dd; original global index 19180.
def localCycle00328 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 0 4, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 3 0, .triangle 2 2, .triangle 13 0, .triangle 29 0, .gapLower 4 0]

-- Original cycle f6f7d4dde0b5c345f681e131c367a7a4fd799886767a9d28355c858411855347; original global index 19263.
def localCycle00329 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .theta 4]
    constant := ![3, -1, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .triangle 4 0, .triangle 2 0, .triangle 16 1, .gapLower 4 0]

-- Original cycle fa4a4e71795004f475bd53d8580b5859b4f715dfdf9b30a82a71a1d91e4a9ae5; original global index 19524.
def localCycle00330 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle faf6b22cff440e7a05b8bf840b3abbfcb7018ff49e0973c77069522b5eac0c81; original global index 19585.
def localCycle00331 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 2, .triangle 18 0, .triangle 0 0, .triangle 3 0, .triangle 17 1, .triangle 28 1, .gapLower 4 0]

-- Original cycle fc13bfc353811fb20032440ce9ee8a3f45b2e28a193a8ecd06893890e5b300ea; original global index 19682.
def localCycle00332 : Cycle where
  length := 4
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .theta 5, .zero]
    constant := ![0, 1, -2, 0]
    coefficient := ![1, 1, -1, 0]
    strict := ![false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapUpper 5 6, .thetaLower 5]

-- Original cycle fc6bcb874ed00557b58c13d291dba536c3166641519666434357de58ea70bac7; original global index 19718.
def localCycle00333 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 2 5, .theta 5]
    constant := ![3, 0, 0, -2, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .triangle 3 0, .triangle 17 1, .gapLower 5 0]

-- Original cycle fca44db5c64385c8106a748eecc449a9e9d93bd8e0a12fc5a1fffd1a025ce3d4; original global index 19738.
def localCycle00334 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.triangle 3 0, .triangle 17 1, .gapUpper 2 3, .gapLower 0 4]

-- Original cycle fcefa6a7db1f5b10b07a5546763f1543a1888f19efd1bc3638ed08a6b1b03f1e; original global index 19763.
def localCycle00335 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 2 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 17 1, .triangle 30 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle fe106ef69d61ed3602cb3f65c49e442a63be04755f624a98d2eea1bd9fadc9f4; original global index 19856.
def localCycle00336 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 0 1, .triangle 3 0, .triangle 17 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle feba907811fa2610acf572dc98dccf1c9bbd51fa519d1c672750558e0379557e; original global index 19918.
def localCycle00337 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 4 2, .triangle 8 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

def library : Library := fun id => if id < 169 then (if id < 84 then (if id < 42 then (if id < 21 then (if id < 10 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 7 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))))) else (if id < 15 then (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)))) else (if id < 18 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none))) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)))))) else (if id < 31 then (if id < 26 then (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)))) else (if id < 28 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none)) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none))))) else (if id < 36 then (if id < 33 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none)) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)))) else (if id < 39 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))))))) else (if id < 63 then (if id < 52 then (if id < 47 then (if id < 44 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none)) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)))) else (if id < 49 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))))) else (if id < 57 then (if id < 54 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)))) else (if id < 60 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)))))) else (if id < 73 then (if id < 68 then (if id < 65 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)))) else (if id < 70 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none))))) else (if id < 78 then (if id < 75 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)))) else (if id < 81 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none))) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)))))))) else (if id < 126 then (if id < 105 then (if id < 94 then (if id < 89 then (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)))) else (if id < 91 then (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none)) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none))))) else (if id < 99 then (if id < 96 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)))) else (if id < 102 then (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none))) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)))))) else (if id < 115 then (if id < 110 then (if id < 107 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none)))) else (if id < 112 then (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none)) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none))))) else (if id < 120 then (if id < 117 then (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)))) else (if id < 123 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none))) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none))))))) else (if id < 147 then (if id < 136 then (if id < 131 then (if id < 128 then (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)))) else (if id < 133 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none)) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none))))) else (if id < 141 then (if id < 138 then (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none)) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none)))) else (if id < 144 then (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none))) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none)))))) else (if id < 158 then (if id < 152 then (if id < 149 then (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none)) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none)))) else (if id < 155 then (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none))) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none))))) else (if id < 163 then (if id < 160 then (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none)) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none)))) else (if id < 166 then (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none))) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none))))))))) else (if id < 253 then (if id < 211 then (if id < 190 then (if id < 179 then (if id < 174 then (if id < 171 then (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none)) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id = 173 then some localCycle00173 else none)))) else (if id < 176 then (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id = 175 then some localCycle00175 else none)) else (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id = 178 then some localCycle00178 else none))))) else (if id < 184 then (if id < 181 then (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none)) else (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id = 183 then some localCycle00183 else none)))) else (if id < 187 then (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none))) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none)))))) else (if id < 200 then (if id < 195 then (if id < 192 then (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id = 191 then some localCycle00191 else none)) else (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none)))) else (if id < 197 then (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none)) else (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none))))) else (if id < 205 then (if id < 202 then (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none)) else (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id = 204 then some localCycle00204 else none)))) else (if id < 208 then (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none))) else (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id = 210 then some localCycle00210 else none))))))) else (if id < 232 then (if id < 221 then (if id < 216 then (if id < 213 then (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id = 212 then some localCycle00212 else none)) else (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none)))) else (if id < 218 then (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id = 217 then some localCycle00217 else none)) else (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id = 220 then some localCycle00220 else none))))) else (if id < 226 then (if id < 223 then (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id = 222 then some localCycle00222 else none)) else (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id = 225 then some localCycle00225 else none)))) else (if id < 229 then (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id < 228 then (if id = 227 then some localCycle00227 else none) else (if id = 228 then some localCycle00228 else none))) else (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id < 231 then (if id = 230 then some localCycle00230 else none) else (if id = 231 then some localCycle00231 else none)))))) else (if id < 242 then (if id < 237 then (if id < 234 then (if id < 233 then (if id = 232 then some localCycle00232 else none) else (if id = 233 then some localCycle00233 else none)) else (if id < 235 then (if id = 234 then some localCycle00234 else none) else (if id < 236 then (if id = 235 then some localCycle00235 else none) else (if id = 236 then some localCycle00236 else none)))) else (if id < 239 then (if id < 238 then (if id = 237 then some localCycle00237 else none) else (if id = 238 then some localCycle00238 else none)) else (if id < 240 then (if id = 239 then some localCycle00239 else none) else (if id < 241 then (if id = 240 then some localCycle00240 else none) else (if id = 241 then some localCycle00241 else none))))) else (if id < 247 then (if id < 244 then (if id < 243 then (if id = 242 then some localCycle00242 else none) else (if id = 243 then some localCycle00243 else none)) else (if id < 245 then (if id = 244 then some localCycle00244 else none) else (if id < 246 then (if id = 245 then some localCycle00245 else none) else (if id = 246 then some localCycle00246 else none)))) else (if id < 250 then (if id < 248 then (if id = 247 then some localCycle00247 else none) else (if id < 249 then (if id = 248 then some localCycle00248 else none) else (if id = 249 then some localCycle00249 else none))) else (if id < 251 then (if id = 250 then some localCycle00250 else none) else (if id < 252 then (if id = 251 then some localCycle00251 else none) else (if id = 252 then some localCycle00252 else none)))))))) else (if id < 295 then (if id < 274 then (if id < 263 then (if id < 258 then (if id < 255 then (if id < 254 then (if id = 253 then some localCycle00253 else none) else (if id = 254 then some localCycle00254 else none)) else (if id < 256 then (if id = 255 then some localCycle00255 else none) else (if id < 257 then (if id = 256 then some localCycle00256 else none) else (if id = 257 then some localCycle00257 else none)))) else (if id < 260 then (if id < 259 then (if id = 258 then some localCycle00258 else none) else (if id = 259 then some localCycle00259 else none)) else (if id < 261 then (if id = 260 then some localCycle00260 else none) else (if id < 262 then (if id = 261 then some localCycle00261 else none) else (if id = 262 then some localCycle00262 else none))))) else (if id < 268 then (if id < 265 then (if id < 264 then (if id = 263 then some localCycle00263 else none) else (if id = 264 then some localCycle00264 else none)) else (if id < 266 then (if id = 265 then some localCycle00265 else none) else (if id < 267 then (if id = 266 then some localCycle00266 else none) else (if id = 267 then some localCycle00267 else none)))) else (if id < 271 then (if id < 269 then (if id = 268 then some localCycle00268 else none) else (if id < 270 then (if id = 269 then some localCycle00269 else none) else (if id = 270 then some localCycle00270 else none))) else (if id < 272 then (if id = 271 then some localCycle00271 else none) else (if id < 273 then (if id = 272 then some localCycle00272 else none) else (if id = 273 then some localCycle00273 else none)))))) else (if id < 284 then (if id < 279 then (if id < 276 then (if id < 275 then (if id = 274 then some localCycle00274 else none) else (if id = 275 then some localCycle00275 else none)) else (if id < 277 then (if id = 276 then some localCycle00276 else none) else (if id < 278 then (if id = 277 then some localCycle00277 else none) else (if id = 278 then some localCycle00278 else none)))) else (if id < 281 then (if id < 280 then (if id = 279 then some localCycle00279 else none) else (if id = 280 then some localCycle00280 else none)) else (if id < 282 then (if id = 281 then some localCycle00281 else none) else (if id < 283 then (if id = 282 then some localCycle00282 else none) else (if id = 283 then some localCycle00283 else none))))) else (if id < 289 then (if id < 286 then (if id < 285 then (if id = 284 then some localCycle00284 else none) else (if id = 285 then some localCycle00285 else none)) else (if id < 287 then (if id = 286 then some localCycle00286 else none) else (if id < 288 then (if id = 287 then some localCycle00287 else none) else (if id = 288 then some localCycle00288 else none)))) else (if id < 292 then (if id < 290 then (if id = 289 then some localCycle00289 else none) else (if id < 291 then (if id = 290 then some localCycle00290 else none) else (if id = 291 then some localCycle00291 else none))) else (if id < 293 then (if id = 292 then some localCycle00292 else none) else (if id < 294 then (if id = 293 then some localCycle00293 else none) else (if id = 294 then some localCycle00294 else none))))))) else (if id < 316 then (if id < 305 then (if id < 300 then (if id < 297 then (if id < 296 then (if id = 295 then some localCycle00295 else none) else (if id = 296 then some localCycle00296 else none)) else (if id < 298 then (if id = 297 then some localCycle00297 else none) else (if id < 299 then (if id = 298 then some localCycle00298 else none) else (if id = 299 then some localCycle00299 else none)))) else (if id < 302 then (if id < 301 then (if id = 300 then some localCycle00300 else none) else (if id = 301 then some localCycle00301 else none)) else (if id < 303 then (if id = 302 then some localCycle00302 else none) else (if id < 304 then (if id = 303 then some localCycle00303 else none) else (if id = 304 then some localCycle00304 else none))))) else (if id < 310 then (if id < 307 then (if id < 306 then (if id = 305 then some localCycle00305 else none) else (if id = 306 then some localCycle00306 else none)) else (if id < 308 then (if id = 307 then some localCycle00307 else none) else (if id < 309 then (if id = 308 then some localCycle00308 else none) else (if id = 309 then some localCycle00309 else none)))) else (if id < 313 then (if id < 311 then (if id = 310 then some localCycle00310 else none) else (if id < 312 then (if id = 311 then some localCycle00311 else none) else (if id = 312 then some localCycle00312 else none))) else (if id < 314 then (if id = 313 then some localCycle00313 else none) else (if id < 315 then (if id = 314 then some localCycle00314 else none) else (if id = 315 then some localCycle00315 else none)))))) else (if id < 327 then (if id < 321 then (if id < 318 then (if id < 317 then (if id = 316 then some localCycle00316 else none) else (if id = 317 then some localCycle00317 else none)) else (if id < 319 then (if id = 318 then some localCycle00318 else none) else (if id < 320 then (if id = 319 then some localCycle00319 else none) else (if id = 320 then some localCycle00320 else none)))) else (if id < 324 then (if id < 322 then (if id = 321 then some localCycle00321 else none) else (if id < 323 then (if id = 322 then some localCycle00322 else none) else (if id = 323 then some localCycle00323 else none))) else (if id < 325 then (if id = 324 then some localCycle00324 else none) else (if id < 326 then (if id = 325 then some localCycle00325 else none) else (if id = 326 then some localCycle00326 else none))))) else (if id < 332 then (if id < 329 then (if id < 328 then (if id = 327 then some localCycle00327 else none) else (if id = 328 then some localCycle00328 else none)) else (if id < 330 then (if id = 329 then some localCycle00329 else none) else (if id < 331 then (if id = 330 then some localCycle00330 else none) else (if id = 331 then some localCycle00331 else none)))) else (if id < 335 then (if id < 333 then (if id = 332 then some localCycle00332 else none) else (if id < 334 then (if id = 333 then some localCycle00333 else none) else (if id = 334 then some localCycle00334 else none))) else (if id < 336 then (if id = 335 then some localCycle00335 else none) else (if id < 337 then (if id = 336 then some localCycle00336 else none) else (if id = 337 then some localCycle00337 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![6, 3, 4, 1, 5, 2], ![6, 3, 4, 0, 5, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 1, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 243 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11008)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 1, 0, 5, 4, 6], ![2, 1, 0, 5, 3, 6], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 230 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11009)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 3], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 43 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11010)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 5, 6, 3], ![0, 1, 2, 4, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 225 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11011)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![0, 1, 2, 6, 4, 3], ![0, 1, 2, 5, 4, 3]], proof := .tail 88 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11012)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 2, 5, 6], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![0, 1, 6, 2, 4, 3], ![0, 1, 5, 2, 4, 3]], proof := .tail 131 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11013)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 1, 2, 4, 3]], proof := .tail 198 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11014)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![3, 4, 1, 2, 6, 5], ![3, 4, 0, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 2, 4, 3]], proof := .tail 87 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11015)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 2, 1, 4, 3]], proof := .tail 157 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11016)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![3, 4, 1, 2, 6, 5], ![3, 4, 0, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 2, 1, 4, 3]], proof := .tail 162 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11017)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![3, 4, 1, 6, 2, 5], ![3, 4, 0, 6, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 0, 1, 4, 3]], proof := .tail 139 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11018)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![3, 4, 6, 1, 2, 5], ![3, 4, 6, 0, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 1, 0, 4, 3]], proof := .tail 234 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11019)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![3, 6, 4, 1, 2, 5], ![3, 4, 6, 0, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 6, 0, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 1, 4, 0, 3]], proof := .tail 86 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11020)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![3, 6, 4, 1, 2, 5], ![3, 6, 4, 0, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 6, 5, 4], ![2, 6, 1, 0, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 4, 1, 0, 3]], proof := .tail 6 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11021)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![3, 6, 4, 1, 2, 5], ![3, 6, 4, 0, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 1, 0, 6, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 318 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11022)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![6, 3, 4, 1, 2, 5], ![3, 4, 6, 0, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 1, 4, 3, 0]], proof := .tail 306 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11023)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![6, 3, 4, 1, 2, 5], ![3, 6, 4, 0, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 6, 0, 5, 4], ![2, 6, 1, 0, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 4, 1, 3, 0]], proof := .tail 6 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11024)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 3, 4, 1, 2, 5], ![3, 6, 4, 0, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 1, 6, 0, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 318 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11025)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![6, 3, 4, 1, 2, 5], ![6, 3, 4, 0, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 6, 1, 0, 5, 4], ![2, 6, 1, 0, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 4, 3, 1, 0]], proof := .tail 140 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11026)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 3, 4, 1, 2, 5], ![6, 3, 4, 0, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 6, 1, 0, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 169 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11027)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 3, 4, 1, 2, 5], ![6, 3, 4, 0, 2, 5], ![6, 3, 4, 0, 1, 5], ![6, 2, 1, 0, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 313 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11028)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 1, 0, 5, 4, 6], ![2, 1, 0, 5, 3, 6], ![0, 2, 1, 4, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 215 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11029)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 1, 0, 5, 4, 6], ![2, 1, 0, 5, 3, 6], ![0, 2, 1, 4, 3, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 241 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11030)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 3], ![0, 2, 1, 4, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 143 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11031)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 5, 6, 3], ![0, 2, 1, 4, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 20 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11032)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![0, 2, 1, 6, 4, 3], ![0, 1, 2, 5, 4, 3]], proof := .tail 129 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11033)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 3], ![0, 2, 1, 4, 3, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 275 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11034)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 5, 6, 3], ![0, 2, 1, 4, 6, 3], ![0, 2, 1, 4, 5, 3]], proof := .tail 274 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11035)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![0, 2, 1, 6, 4, 3], ![0, 2, 1, 5, 4, 3]], proof := .tail 129 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11036)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 6, 5, 2], ![3, 4, 0, 5, 6, 1], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![0, 2, 6, 1, 4, 3], ![0, 2, 5, 1, 4, 3]], proof := .tail 128 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11037)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 6, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![0, 6, 2, 1, 4, 3], ![0, 5, 2, 1, 4, 3]], proof := .tail 115 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11038)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![3, 4, 1, 2, 6, 5], ![3, 4, 0, 6, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 0, 2, 1, 4, 3]], proof := .tail 74 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11039)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![3, 4, 1, 6, 2, 5], ![3, 4, 0, 6, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 2, 0, 1, 4, 3]], proof := .tail 71 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11040)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![3, 4, 6, 1, 2, 5], ![3, 4, 6, 0, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 2, 1, 0, 4, 3]], proof := .tail 15 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11041)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![3, 6, 4, 1, 2, 5], ![3, 4, 6, 0, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 0, 6, 5, 4], ![2, 1, 6, 0, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 2, 1, 4, 0, 3]], proof := .tail 328 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11042)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![3, 6, 4, 1, 2, 5], ![3, 6, 4, 0, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 0, 6, 5, 4], ![2, 6, 1, 0, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 2, 4, 1, 0, 3]], proof := .tail 295 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11043)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![3, 6, 4, 1, 2, 5], ![3, 6, 4, 0, 5, 2], ![3, 6, 4, 0, 5, 1], ![2, 1, 0, 6, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 220 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11044)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![6, 3, 4, 1, 2, 5], ![3, 4, 6, 0, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 2, 1, 4, 3, 0]], proof := .tail 314 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11045)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![6, 3, 4, 1, 2, 5], ![3, 6, 4, 0, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 6, 0, 5, 4], ![2, 6, 1, 0, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 2, 4, 1, 3, 0]], proof := .tail 295 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11046)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![6, 3, 4, 1, 2, 5], ![3, 6, 4, 0, 5, 2], ![3, 6, 4, 0, 5, 1], ![2, 1, 6, 0, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 220 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11047)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![6, 3, 4, 1, 2, 5], ![6, 3, 4, 0, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 6, 1, 0, 5, 4], ![2, 6, 1, 0, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 2, 4, 3, 1, 0]], proof := .tail 205 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11048)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![6, 3, 4, 1, 2, 5], ![6, 3, 4, 0, 5, 2], ![3, 6, 4, 0, 5, 1], ![2, 6, 1, 0, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 205 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11049)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![6, 3, 4, 1, 2, 5], ![6, 3, 4, 0, 5, 2], ![6, 3, 4, 0, 5, 1], ![6, 2, 1, 0, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 236 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11050)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![3, 4, 1, 5, 2, 6], ![3, 4, 0, 5, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 1, 0, 5, 4, 6], ![2, 1, 0, 5, 3, 6], ![2, 0, 1, 4, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 253 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11051)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![3, 4, 1, 5, 2, 6], ![3, 4, 0, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 5, 4, 6], ![2, 1, 0, 5, 3, 6], ![2, 0, 1, 4, 3, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 278 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11052)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![3, 4, 1, 5, 6, 2], ![3, 4, 0, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 5, 4, 6], ![2, 1, 0, 5, 3, 6], ![2, 0, 1, 4, 3, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 253 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11053)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![3, 4, 1, 5, 2, 6], ![3, 4, 0, 5, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 3], ![2, 0, 1, 4, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 72 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11054)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![3, 4, 1, 5, 2, 6], ![3, 4, 0, 5, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 5, 6, 3], ![2, 0, 1, 4, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 274 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11055)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![3, 4, 1, 5, 2, 6], ![3, 4, 0, 5, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![2, 0, 1, 6, 4, 3], ![0, 1, 2, 5, 4, 3]], proof := .tail 129 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11056)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![3, 4, 1, 5, 2, 6], ![3, 4, 0, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 3], ![2, 0, 1, 4, 3, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 24 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11057)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![3, 4, 1, 5, 2, 6], ![3, 4, 0, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 5, 6, 3], ![2, 0, 1, 4, 6, 3], ![0, 2, 1, 4, 5, 3]], proof := .tail 274 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11058)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![3, 4, 1, 5, 2, 6], ![3, 4, 0, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![2, 0, 1, 6, 4, 3], ![0, 2, 1, 5, 4, 3]], proof := .tail 129 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11059)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![3, 4, 1, 5, 2, 6], ![3, 4, 0, 6, 5, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![2, 0, 6, 1, 4, 3], ![0, 2, 5, 1, 4, 3]], proof := .tail 262 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11060)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![3, 4, 1, 5, 6, 2], ![3, 4, 0, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 3], ![2, 0, 1, 4, 3, 6], ![2, 0, 1, 4, 3, 5]], proof := .low6 (![161, 9, 258, 252, 184, 217, 200, 168, 30, 329, 50, 233, 80, 199, 312, 221, 232, 160, 130, 267, 317, 172, 27, 65, 329, 291, 208, 260]) }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11061)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![3, 4, 1, 5, 6, 2], ![3, 4, 0, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 5, 6, 3], ![2, 0, 1, 4, 6, 3], ![2, 0, 1, 4, 5, 3]], proof := .tail 274 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11062)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![3, 4, 1, 5, 6, 2], ![3, 4, 0, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![2, 0, 1, 6, 4, 3], ![2, 0, 1, 5, 4, 3]], proof := .tail 129 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11063)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![3, 4, 1, 5, 6, 2], ![3, 4, 0, 6, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![2, 0, 6, 1, 4, 3], ![2, 0, 5, 1, 4, 3]], proof := .tail 79 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11064)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![3, 4, 1, 6, 5, 2], ![3, 4, 0, 6, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![2, 6, 0, 1, 4, 3], ![2, 5, 0, 1, 4, 3]], proof := .low6 (![147, 117, 285, 7, 180, 214, 219, 133, 57, 303, 22, 321, 94, 11, 238, 238, 321, 238, 17, 25, 321, 21, 119, 19, 41, 67, 22, 321]) }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11065)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![3, 4, 1, 6, 5, 2], ![3, 4, 0, 6, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 2, 0, 1, 4, 3]], proof := .low6 (![110, 235, 237, 7, 180, 214, 286, 112, 254, 222, 22, 321, 118, 266, 197, 337, 321, 273, 320, 182, 321, 307, 119, 19, 209, 67, 22, 321]) }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11066)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![3, 4, 6, 1, 5, 2], ![3, 4, 6, 0, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![2, 6, 0, 1, 4, 3], ![2, 5, 1, 0, 4, 3]], proof := .tail 28 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11067)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![3, 6, 4, 1, 5, 2], ![3, 4, 6, 0, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 1, 6, 0, 5, 3], ![2, 6, 0, 1, 4, 3], ![2, 5, 1, 4, 0, 3]], proof := .tail 102 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11068)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![3, 6, 4, 1, 5, 2], ![3, 6, 4, 0, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 6, 1, 0, 5, 3], ![2, 6, 0, 1, 4, 3], ![2, 5, 4, 1, 0, 3]], proof := .tail 295 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11069)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![6, 3, 4, 1, 5, 2], ![3, 4, 6, 0, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 3], ![2, 6, 0, 1, 4, 3], ![2, 5, 1, 4, 3, 0]], proof := .tail 102 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11070)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![6, 3, 4, 1, 5, 2], ![3, 6, 4, 0, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 6, 0, 5, 4], ![2, 6, 1, 0, 5, 3], ![2, 6, 0, 1, 4, 3], ![2, 5, 4, 1, 3, 0]], proof := .tail 295 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11071)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![6, 3, 4, 1, 5, 2], ![6, 3, 4, 0, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 1, 0, 5, 4], ![2, 6, 1, 0, 5, 3], ![2, 6, 0, 1, 4, 3], ![2, 5, 4, 3, 1, 0]], proof := .tail 205 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11072)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![3, 4, 6, 1, 5, 2], ![3, 4, 6, 0, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 2, 1, 0, 4, 3]], proof := .tail 15 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11073)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![3, 6, 4, 1, 5, 2], ![3, 4, 6, 0, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 1, 6, 0, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 2, 1, 4, 0, 3]], proof := .tail 247 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11074)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![3, 6, 4, 1, 5, 2], ![3, 6, 4, 0, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 6, 1, 0, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 2, 4, 1, 0, 3]], proof := .tail 295 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11075)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![3, 6, 4, 1, 5, 2], ![3, 6, 4, 0, 5, 2], ![3, 6, 4, 5, 0, 1], ![2, 1, 0, 6, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 220 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11076)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![6, 3, 4, 1, 5, 2], ![3, 4, 6, 0, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 2, 1, 4, 3, 0]], proof := .tail 247 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11077)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![6, 3, 4, 1, 5, 2], ![3, 6, 4, 0, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 6, 0, 5, 4], ![2, 6, 1, 0, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 2, 4, 1, 3, 0]], proof := .tail 295 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11078)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![6, 3, 4, 1, 5, 2], ![3, 6, 4, 0, 5, 2], ![3, 6, 4, 5, 0, 1], ![2, 1, 6, 0, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 220 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11079)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![6, 3, 4, 1, 5, 2], ![6, 3, 4, 0, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 1, 0, 5, 4], ![2, 6, 1, 0, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 2, 4, 3, 1, 0]], proof := .tail 205 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11080)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 3, 4, 1, 5, 2], ![6, 3, 4, 0, 5, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 1, 0, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 205 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11081)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![6, 3, 4, 1, 5, 2], ![6, 3, 4, 0, 5, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 1, 0, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 236 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11082)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![3, 4, 5, 1, 2, 6], ![3, 4, 5, 0, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 1, 0, 4, 5, 6], ![2, 1, 0, 3, 5, 6], ![2, 1, 0, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .low0 (![127, 216, 89, 23, 179, 302, 13, 126, 256, 151, 334, 191, 191, 124, 126, 126, 126, 126, 288, 334, 227, 187, 0, 176, 92, 334, 334, 62]) }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11083)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![3, 4, 5, 1, 2, 6], ![3, 4, 5, 0, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 1, 0, 4, 5, 6], ![2, 1, 0, 3, 6, 5], ![2, 1, 0, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 277 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11084)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![3, 4, 5, 1, 2, 6], ![3, 4, 5, 0, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![2, 1, 0, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 150 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11085)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![3, 4, 5, 1, 2, 6], ![3, 4, 5, 0, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![2, 1, 0, 6, 3, 4], ![0, 1, 2, 5, 4, 3]], proof := .tail 289 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11086)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![3, 4, 5, 1, 2, 6], ![3, 4, 5, 0, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 4, 5, 6], ![2, 1, 0, 3, 5, 6], ![2, 1, 0, 3, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 336 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11087)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![3, 4, 5, 1, 2, 6], ![3, 4, 5, 0, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 4, 5, 6], ![2, 1, 0, 3, 6, 5], ![2, 1, 0, 3, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 336 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11088)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![3, 4, 5, 1, 2, 6], ![3, 4, 5, 0, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![2, 1, 0, 6, 3, 4], ![0, 2, 1, 5, 3, 4]], proof := .tail 336 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11089)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![3, 4, 5, 1, 2, 6], ![3, 4, 5, 0, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![2, 1, 0, 6, 3, 4], ![0, 2, 1, 5, 4, 3]], proof := .tail 164 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11090)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![3, 4, 5, 1, 6, 2], ![3, 4, 5, 0, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 4, 5, 6], ![2, 1, 0, 3, 5, 6], ![2, 1, 0, 3, 4, 6], ![2, 0, 1, 3, 4, 5]], proof := .low6 (![202, 9, 299, 29, 78, 84, 149, 100, 192, 242, 64, 325, 259, 199, 108, 49, 26, 18, 153, 250, 297, 95, 311, 323, 125, 38, 301, 251]) }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11091)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![3, 4, 5, 1, 6, 2], ![3, 4, 5, 0, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 4, 5, 6], ![2, 1, 0, 3, 6, 5], ![2, 1, 0, 3, 6, 4], ![2, 0, 1, 3, 5, 4]], proof := .low0 (![327, 216, 188, 23, 93, 53, 116, 126, 206, 175, 148, 300, 300, 105, 126, 126, 126, 126, 32, 158, 47, 106, 268, 96, 97, 310, 81, 152]) }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11092)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![3, 4, 5, 1, 6, 2], ![3, 4, 5, 0, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![2, 1, 0, 6, 3, 4], ![2, 0, 1, 5, 3, 4]], proof := .twoLow (![some 293, some 216, some 156, some 276, some 93, some 53, some 203, some 126, some 155, some 40, some 304, some 56, none, some 105, some 126, some 126, some 126, some 126, some 32, some 158, some 47, some 305, some 83, some 5, some 40, some 310, some 81, some 152]) (![some 194, some 9, some 299, some 195, some 73, some 16, some 224, some 77, some 248, some 82, some 298, some 296, none, some 199, some 319, some 189, some 33, some 137, some 173, some 45, some 261, some 193, some 333, some 240, some 319, some 322, some 264, some 36]) (fun p0 p6 => if p0 = 12 ∧ p6 = 12 then 138 else (0)) }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11093)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![3, 4, 5, 1, 6, 2], ![3, 4, 5, 0, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![2, 1, 0, 6, 3, 4], ![2, 0, 1, 5, 4, 3]], proof := .tail 167 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11094)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![3, 4, 5, 6, 1, 2], ![3, 4, 5, 6, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 4, 5, 6], ![2, 1, 0, 3, 5, 6], ![2, 1, 0, 3, 4, 6], ![2, 1, 0, 3, 4, 5]], proof := .low0 (![127, 216, 196, 269, 104, 122, 211, 126, 244, 135, 257, 316, 191, 42, 126, 126, 126, 126, 109, 51, 316, 280, 142, 316, 58, 316, 271, 316]) }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11095)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![3, 4, 5, 6, 1, 2], ![3, 4, 5, 6, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 4, 5, 6], ![2, 1, 0, 3, 6, 5], ![2, 1, 0, 3, 6, 4], ![2, 1, 0, 3, 5, 4]], proof := .low0 (![327, 216, 188, 269, 104, 122, 211, 126, 206, 135, 257, 316, 300, 85, 126, 126, 126, 126, 109, 51, 316, 106, 142, 316, 58, 316, 271, 316]) }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11096)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![3, 4, 5, 6, 1, 2], ![3, 4, 5, 6, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![2, 1, 0, 6, 3, 4], ![2, 1, 0, 5, 3, 4]], proof := .low6 (![212, 2, 165, 34, 73, 16, 224, 324, 76, 229, 1, 63, 290, 141, 324, 324, 324, 37, 121, 287, 270, 218, 60, 210, 66, 322, 103, 70]) }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11097)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![3, 4, 6, 5, 1, 2], ![3, 4, 5, 6, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![2, 1, 6, 0, 3, 4], ![2, 1, 5, 0, 3, 4]], proof := .tail 146 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11098)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![3, 4, 6, 5, 1, 2], ![3, 4, 6, 5, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![2, 6, 1, 0, 3, 4], ![2, 5, 1, 0, 3, 4]], proof := .tail 174 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11099)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![3, 4, 6, 5, 1, 2], ![3, 4, 6, 5, 0, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![6, 2, 1, 0, 3, 4], ![5, 2, 1, 0, 3, 4]], proof := .tail 166 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11100)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![3, 4, 5, 6, 1, 2], ![3, 4, 5, 6, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![2, 1, 0, 6, 3, 4], ![2, 1, 0, 5, 4, 3]], proof := .low0 (![283, 54, 170, 186, 104, 122, 201, 136, 3, 44, 263, 316, 178, 3, 111, 231, 59, 59, 308, 3, 3, 3, 142, 316, 120, 316, 271, 316]) }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11101)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![3, 4, 6, 5, 1, 2], ![3, 4, 5, 6, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![2, 1, 6, 0, 3, 4], ![2, 1, 5, 0, 4, 3]], proof := .tail 146 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11102)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![3, 4, 6, 5, 1, 2], ![3, 4, 6, 5, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![2, 6, 1, 0, 3, 4], ![2, 5, 1, 0, 4, 3]], proof := .tail 174 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11103)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![3, 4, 6, 5, 1, 2], ![3, 4, 6, 5, 0, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![6, 2, 1, 0, 3, 4], ![5, 2, 1, 0, 4, 3]], proof := .tail 134 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11104)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![3, 6, 4, 5, 1, 2], ![3, 4, 5, 6, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 6, 0, 3, 5], ![2, 1, 6, 0, 3, 4], ![2, 1, 5, 4, 0, 3]], proof := .tail 4 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11105)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![3, 6, 4, 5, 1, 2], ![3, 4, 6, 5, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 6, 0, 3, 5], ![2, 6, 1, 0, 3, 4], ![2, 5, 1, 4, 0, 3]], proof := .tail 174 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11106)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![3, 6, 4, 5, 1, 2], ![3, 4, 6, 5, 0, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 6, 0, 3, 5], ![6, 2, 1, 0, 3, 4], ![5, 2, 1, 4, 0, 3]], proof := .tail 4 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11107)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![3, 6, 4, 5, 1, 2], ![3, 6, 4, 5, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 4, 5], ![2, 6, 1, 0, 3, 5], ![2, 6, 1, 0, 3, 4], ![2, 5, 4, 1, 0, 3]], proof := .tail 144 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11108)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![3, 6, 4, 5, 1, 2], ![3, 6, 4, 5, 0, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 0, 6, 4, 5], ![2, 6, 1, 0, 3, 5], ![6, 2, 1, 0, 3, 4], ![5, 2, 4, 1, 0, 3]], proof := .tail 144 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11109)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![3, 6, 4, 5, 1, 2], ![3, 6, 4, 5, 0, 2], ![3, 6, 4, 5, 0, 1], ![2, 1, 0, 6, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 2, 1, 0, 3, 4], ![5, 4, 2, 1, 0, 3]], proof := .tail 239 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11110)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![6, 3, 4, 5, 1, 2], ![3, 4, 5, 6, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 3, 5], ![2, 1, 6, 0, 3, 4], ![2, 1, 5, 4, 3, 0]], proof := .tail 177 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11111)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 3, 4, 5, 1, 2], ![3, 4, 6, 5, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 3, 5], ![2, 6, 1, 0, 3, 4], ![2, 5, 1, 4, 3, 0]], proof := .tail 174 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11112)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 3, 4, 5, 1, 2], ![3, 4, 6, 5, 0, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 3, 5], ![6, 2, 1, 0, 3, 4], ![5, 2, 1, 4, 3, 0]], proof := .tail 335 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11113)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 3, 4, 5, 1, 2], ![3, 6, 4, 5, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 6, 0, 4, 5], ![2, 6, 1, 0, 3, 5], ![2, 6, 1, 0, 3, 4], ![2, 5, 4, 1, 3, 0]], proof := .tail 144 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11114)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 3, 4, 5, 1, 2], ![3, 6, 4, 5, 0, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 6, 0, 4, 5], ![2, 6, 1, 0, 3, 5], ![6, 2, 1, 0, 3, 4], ![5, 2, 4, 1, 3, 0]], proof := .tail 144 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11115)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 3, 4, 5, 1, 2], ![3, 6, 4, 5, 0, 2], ![3, 6, 4, 5, 0, 1], ![2, 1, 6, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 2, 1, 0, 3, 4], ![5, 4, 2, 1, 3, 0]], proof := .tail 132 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11116)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 3, 4, 5, 1, 2], ![6, 3, 4, 5, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 1, 0, 4, 5], ![2, 6, 1, 0, 3, 5], ![2, 6, 1, 0, 3, 4], ![2, 5, 4, 3, 1, 0]], proof := .tail 294 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11117)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 3, 4, 5, 1, 2], ![6, 3, 4, 5, 0, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 1, 0, 4, 5], ![2, 6, 1, 0, 3, 5], ![6, 2, 1, 0, 3, 4], ![5, 2, 4, 3, 1, 0]], proof := .tail 294 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11118)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 3, 4, 5, 1, 2], ![6, 3, 4, 5, 0, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 1, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 2, 1, 0, 3, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 294 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11119)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 3, 4, 5, 1, 2], ![6, 3, 4, 5, 0, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 1, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 2, 1, 0, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 326 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11120)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![3, 4, 5, 1, 2, 6], ![3, 4, 5, 0, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 1, 0, 5, 4, 6], ![2, 1, 0, 5, 3, 6], ![2, 1, 0, 4, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .low0 (![246, 171, 90, 23, 179, 302, 13, 68, 75, 151, 334, 163, 163, 284, 68, 68, 68, 68, 288, 75, 75, 75, 0, 176, 92, 334, 334, 62]) }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11121)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![3, 4, 5, 1, 2, 6], ![3, 4, 5, 0, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 3], ![2, 1, 0, 4, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 159 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11122)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![3, 4, 5, 1, 2, 6], ![3, 4, 5, 0, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 5, 6, 3], ![2, 1, 0, 4, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 331 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11123)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![3, 4, 5, 1, 2, 6], ![3, 4, 5, 0, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![2, 1, 0, 6, 4, 3], ![0, 1, 2, 5, 4, 3]], proof := .tail 190 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11124)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![3, 4, 5, 1, 2, 6], ![3, 4, 5, 0, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 5, 4, 6], ![2, 1, 0, 5, 3, 6], ![2, 1, 0, 4, 3, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 336 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11125)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![3, 4, 5, 1, 2, 6], ![3, 4, 5, 0, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 3], ![2, 1, 0, 4, 3, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 336 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11126)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![3, 4, 5, 1, 2, 6], ![3, 4, 5, 0, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 5, 6, 3], ![2, 1, 0, 4, 6, 3], ![0, 2, 1, 4, 5, 3]], proof := .tail 336 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11127)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![3, 4, 5, 1, 2, 6], ![3, 4, 5, 0, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![2, 1, 0, 6, 4, 3], ![0, 2, 1, 5, 4, 3]], proof := .tail 55 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11128)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![3, 4, 5, 1, 6, 2], ![3, 4, 5, 0, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 5, 4, 6], ![2, 1, 0, 5, 3, 6], ![2, 1, 0, 4, 3, 6], ![2, 0, 1, 3, 4, 5]], proof := .low6 (![265, 9, 299, 29, 272, 14, 107, 100, 192, 242, 64, 181, 204, 199, 108, 31, 181, 91, 153, 250, 181, 95, 311, 181, 125, 61, 301, 181]) }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11129)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![3, 4, 5, 1, 6, 2], ![3, 4, 5, 0, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 3], ![2, 1, 0, 4, 3, 6], ![2, 0, 1, 4, 3, 5]], proof := .twoLow (![some 46, some 171, some 90, some 23, some 93, some 53, some 203, some 68, some 75, some 175, some 39, some 56, none, some 284, some 68, some 68, some 68, some 68, some 32, some 75, some 75, some 75, some 268, some 213, some 97, some 310, some 81, some 152]) (![some 309, some 9, some 299, some 48, some 184, some 217, some 69, some 168, some 12, some 249, some 50, some 233, none, some 199, some 281, some 221, some 232, some 137, some 8, some 315, some 317, some 223, some 183, some 249, some 249, some 10, some 245, some 98]) (fun p0 p6 => if p0 = 12 ∧ p6 = 12 then 226 else (0)) }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11130)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![3, 4, 5, 1, 6, 2], ![3, 4, 5, 0, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 5, 6, 3], ![2, 1, 0, 4, 6, 3], ![2, 0, 1, 4, 5, 3]], proof := .tail 52 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11131)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![3, 4, 5, 1, 6, 2], ![3, 4, 5, 0, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![2, 1, 0, 6, 4, 3], ![2, 0, 1, 5, 4, 3]], proof := .tail 145 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11132)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![3, 4, 5, 6, 1, 2], ![3, 4, 5, 6, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 5, 4, 6], ![2, 1, 0, 5, 3, 6], ![2, 1, 0, 4, 3, 6], ![2, 1, 0, 3, 4, 5]], proof := .low0 (![246, 171, 90, 269, 104, 122, 211, 68, 154, 135, 257, 316, 163, 284, 68, 68, 68, 68, 109, 75, 75, 75, 142, 316, 58, 316, 271, 316]) }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11133)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![3, 4, 5, 6, 1, 2], ![3, 4, 5, 6, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 3], ![2, 1, 0, 4, 3, 6], ![2, 1, 0, 4, 3, 5]], proof := .twoLow (![some 46, some 171, some 90, some 269, some 104, some 122, some 201, some 68, some 75, some 135, some 257, some 316, none, some 284, some 68, some 68, some 68, some 68, some 109, some 75, some 75, some 75, some 142, some 316, some 58, some 316, some 271, some 316]) (![some 212, some 2, some 165, some 282, some 184, some 217, some 332, some 324, some 101, some 207, some 228, some 185, some 255, some 141, some 324, some 324, some 37, some 37, some 114, some 99, some 113, some 218, some 279, some 123, none, some 10, some 292, some 330]) (fun p0 p6 => if p0 = 12 ∧ p6 = 24 then 35 else (0)) }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11134)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![3, 4, 5, 6, 1, 2], ![3, 4, 5, 6, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 5, 6, 3], ![2, 1, 0, 4, 6, 3], ![2, 1, 0, 4, 5, 3]], proof := .tail 52 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11135)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (11008 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 11008 ≤ id.val) (hhigh : id.val < 11136) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 11008)) = true := by
  let j : Fin 128 := ⟨id.val - 11008, by omega⟩
  have hsum : 11008 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (11008 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard086
